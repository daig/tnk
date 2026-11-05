use std::panic::{AssertUnwindSafe, catch_unwind};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::{Arc, Mutex};

use tnk_core::dag::{DagId, NodeRepr};
use tnk_core::engine::{Engine, RewriteKind, TraceEvent};
use tnk_core::host::{
    HookSort, HostBindingError, HostFunctionCatalog, ReducerFault, ResolvedHostHooks, StrictCall,
    StrictOutcome, StrictReduceCtx, StrictReducer, StrictReducerDescriptor, codecs,
};
use tnk_core::search::Arrow;
use tnk_core::sort::SortId;
use tnk_core::symbol::{NatHooks, SpecialOp, SymbolClass, SymbolId};
use tnk_core::term::{ConditionFragment, Equation, Membership, Term};

#[derive(Clone)]
struct ReuseReducer {
    calls: Arc<AtomicUsize>,
}

impl StrictReducer for ReuseReducer {
    fn reduce<'ctx>(
        &self,
        ctx: &mut StrictReduceCtx<'ctx>,
        call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        self.calls.fetch_add(1, Ordering::SeqCst);
        if call.arguments().len() != 1
            || call.argument_sorts()[0] != call.result_range()
            || !ctx.is_ground(call.argument(0))
        {
            return Err(ReducerFault::new("unexpected strict-call contract"));
        }
        Ok(StrictOutcome::Reduced(ctx.reuse(call.argument(0))))
    }
}

#[derive(Clone)]
struct DeclineCounter {
    calls: Arc<AtomicUsize>,
}

impl StrictReducer for DeclineCounter {
    fn reduce<'ctx>(
        &self,
        _ctx: &mut StrictReduceCtx<'ctx>,
        _call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        self.calls.fetch_add(1, Ordering::SeqCst);
        Ok(StrictOutcome::Decline)
    }
}

#[derive(Clone)]
struct SelectArgument {
    index: usize,
    calls: Arc<AtomicUsize>,
}

impl StrictReducer for SelectArgument {
    fn reduce<'ctx>(
        &self,
        ctx: &mut StrictReduceCtx<'ctx>,
        call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        self.calls.fetch_add(1, Ordering::SeqCst);
        Ok(StrictOutcome::Reduced(ctx.reuse(call.argument(self.index))))
    }
}

#[derive(Clone, Copy)]
struct ReturnFirstArgument;

impl StrictReducer for ReturnFirstArgument {
    fn reduce<'ctx>(
        &self,
        ctx: &mut StrictReduceCtx<'ctx>,
        call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        Ok(StrictOutcome::Reduced(ctx.reuse(call.argument(0))))
    }
}

#[derive(Clone)]
struct WrapReducer {
    calls: Arc<AtomicUsize>,
}

impl StrictReducer for WrapReducer {
    fn reduce<'ctx>(
        &self,
        ctx: &mut StrictReduceCtx<'ctx>,
        call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        self.calls.fetch_add(1, Ordering::SeqCst);
        let wrap = call.hooks().op_symbol("wrapSymbol");
        let first = ctx.app(wrap, &[call.argument(0).as_ref()])?;
        let second = ctx.app(wrap, &[first.as_ref()])?;
        Ok(StrictOutcome::Reduced(second))
    }
}

#[derive(Clone, Copy)]
struct BuildOnce;

impl StrictReducer for BuildOnce {
    fn reduce<'ctx>(
        &self,
        ctx: &mut StrictReduceCtx<'ctx>,
        call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        let symbol = call.hooks().op_symbol("resultSymbol");
        Ok(StrictOutcome::Reduced(
            ctx.app(symbol, &[call.argument(0).as_ref()])?,
        ))
    }
}

#[derive(Clone, Copy)]
struct ActiveHookUse;

impl StrictReducer for ActiveHookUse {
    fn reduce<'ctx>(
        &self,
        ctx: &mut StrictReduceCtx<'ctx>,
        call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        let hooks = call.hooks();
        let constant_symbol = hooks.term_symbol("constantTerm");
        if !constant_symbol.matches(ctx.top(call.argument(0).as_ref())) {
            return Err(ReducerFault::new(
                "active constant hook did not match the argument",
            ));
        }
        let constant = ctx.constant(constant_symbol)?;
        let wrapper = hooks.op_symbol("wrapperSymbol");
        Ok(StrictOutcome::Reduced(
            ctx.app(wrapper, &[constant.as_ref()])?,
        ))
    }
}

#[derive(Clone)]
struct ExpectTop {
    symbol: Arc<Mutex<Option<SymbolId>>>,
    calls: Arc<AtomicUsize>,
}

impl StrictReducer for ExpectTop {
    fn reduce<'ctx>(
        &self,
        ctx: &mut StrictReduceCtx<'ctx>,
        call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        self.calls.fetch_add(1, Ordering::SeqCst);
        let expected = self
            .symbol
            .lock()
            .expect("expected-symbol lock")
            .expect("expected symbol installed");
        if ctx.top(call.argument(0).as_ref()) != expected {
            return Err(ReducerFault::new(
                "callback did not receive the forwarded normal form",
            ));
        }
        Ok(StrictOutcome::Reduced(ctx.reuse(call.argument(0))))
    }
}

#[derive(Clone, Copy)]
struct ArgumentShape {
    root: SymbolId,
    first_child: Option<SymbolId>,
    child_count: usize,
}

#[derive(Clone)]
struct InspectArgumentShape {
    expected: Arc<Mutex<Option<ArgumentShape>>>,
    calls: Arc<AtomicUsize>,
}

impl StrictReducer for InspectArgumentShape {
    fn reduce<'ctx>(
        &self,
        ctx: &mut StrictReduceCtx<'ctx>,
        call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        self.calls.fetch_add(1, Ordering::SeqCst);
        if call.arguments().len() != 1 {
            return Err(ReducerFault::new(
                "shape observer did not receive exactly one direct argument",
            ));
        }
        let expected = self
            .expected
            .lock()
            .expect("expected-shape lock")
            .expect("expected shape installed");
        let argument = call.argument(0);
        if ctx.top(argument.as_ref()) != expected.root {
            return Err(ReducerFault::new(
                "shape observer received the wrong argument root",
            ));
        }
        let mut children = ctx.children(argument.as_ref());
        let first_child = children.next();
        let child_count = usize::from(first_child.is_some()) + children.count();
        if child_count != expected.child_count {
            return Err(ReducerFault::new(
                "shape observer received the wrong canonical child count",
            ));
        }
        if let Some(expected_child) = expected.first_child {
            let child = first_child
                .ok_or_else(|| ReducerFault::new("shape observer expected a suspended child"))?;
            if ctx.top(child) != expected_child {
                return Err(ReducerFault::new(
                    "shape observer's suspended child was reduced",
                ));
            }
        }
        Ok(StrictOutcome::Reduced(ctx.reuse(argument)))
    }
}

#[derive(Clone, Copy)]
struct FaultReducer;

impl StrictReducer for FaultReducer {
    fn reduce<'ctx>(
        &self,
        _ctx: &mut StrictReduceCtx<'ctx>,
        _call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        Err(ReducerFault::new("identity fault"))
    }
}

#[derive(Clone, Copy)]
struct BuildThroughIdentity;

impl StrictReducer for BuildThroughIdentity {
    fn reduce<'ctx>(
        &self,
        ctx: &mut StrictReduceCtx<'ctx>,
        call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        let identity = ctx.constant(call.hooks().term_symbol("identityTerm"))?;
        let plus = call.hooks().op_symbol("plusSymbol");
        let result = ctx.app(plus, &[identity.as_ref(), identity.as_ref()])?;
        Ok(StrictOutcome::Reduced(result))
    }
}

#[derive(Clone, Copy)]
struct BuildCanonicalTheories;

impl StrictReducer for BuildCanonicalTheories {
    fn reduce<'ctx>(
        &self,
        ctx: &mut StrictReduceCtx<'ctx>,
        call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        let identity_symbol = call.hooks().term_symbol("identityTerm");
        let value_symbol = call.hooks().term_symbol("valueTerm");
        let acu_symbol = call.hooks().op_symbol("acuSymbol");
        let au_symbol = call.hooks().op_symbol("auSymbol");
        let cui_symbol = call.hooks().op_symbol("cuiSymbol");
        let identity = ctx.constant(identity_symbol)?;
        let value = ctx.constant(value_symbol)?;
        let acu = ctx.app(acu_symbol, &[identity.as_ref(), value.as_ref()])?;
        let au = ctx.app(au_symbol, &[identity.as_ref(), acu.as_ref()])?;
        let cui = ctx.app(cui_symbol, &[au.as_ref(), au.as_ref()])?;
        Ok(StrictOutcome::Reduced(cui))
    }
}

#[derive(Clone, Copy)]
struct PanicReducer;

impl StrictReducer for PanicReducer {
    fn reduce<'ctx>(
        &self,
        _ctx: &mut StrictReduceCtx<'ctx>,
        _call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        panic!("trusted reducer panic")
    }
}

fn no_hooks() -> ResolvedHostHooks {
    ResolvedHostHooks::builder()
        .build()
        .expect("empty hook table")
}

fn unary_descriptor() -> StrictReducerDescriptor {
    StrictReducerDescriptor::builder(1).build()
}

fn unary_engine(catalog: HostFunctionCatalog, key: &str) -> (Engine, SortId, SymbolId, SymbolId) {
    let mut engine = Engine::with_host_functions(catalog);
    let sort = engine.add_sort("S");
    engine.close_sorts();
    let constant = engine.add_op("a", vec![], sort);
    let host = engine.add_op("host", vec![sort], sort);
    engine
        .bind_host_function(host, key, no_hooks())
        .expect("bind unary host function");
    (engine, sort, constant, host)
}

#[test]
fn catalog_is_shareable_and_normal_form_cache_invokes_host_once() {
    fn assert_send_sync_static<T: Send + Sync + 'static>() {}
    fn assert_reducer<T: StrictReducer>() {}
    assert_send_sync_static::<HostFunctionCatalog>();
    assert_reducer::<ReuseReducer>();
    assert_reducer::<WrapReducer>();

    let calls = Arc::new(AtomicUsize::new(0));
    let catalog = HostFunctionCatalog::builder()
        .register(
            "cache.observe",
            ReuseReducer {
                calls: Arc::clone(&calls),
            },
            unary_descriptor(),
        )
        .expect("register observing reducer")
        .build();

    for _ in 0..2 {
        let (mut engine, _, constant, host) = unary_engine(catalog.clone(), "cache.observe");
        let argument = engine.make_const(constant);
        let redex = engine.make_free(host, vec![argument]);
        assert_eq!(engine.try_reduce(redex).expect("first reduction"), argument);
        engine.reset_rewrites();
        assert_eq!(
            engine.try_reduce(redex).expect("cached reduction"),
            argument
        );
        assert_eq!(engine.rewrites(), 0, "cached reduction adds no rewrite");
    }
    assert_eq!(calls.load(Ordering::SeqCst), 2, "one call per Engine");
}

#[test]
fn callback_construction_is_gc_safe_and_trace_identifies_host_key() {
    let calls = Arc::new(AtomicUsize::new(0));
    let descriptor = StrictReducerDescriptor::builder(1)
        .require_op_hook("wrapSymbol", &[HookSort::Argument(0)], HookSort::Result)
        .build();
    let catalog = HostFunctionCatalog::builder()
        .register(
            "gc.wrap-twice",
            WrapReducer {
                calls: Arc::clone(&calls),
            },
            descriptor,
        )
        .expect("register allocating reducer")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let sort = engine.add_sort("S");
    let truth = engine.add_sort("Truth");
    engine.close_sorts();
    let constant = engine.add_op("a", vec![], sort);
    let true_term = engine.add_op("true", vec![], truth);
    let false_term = engine.add_op("false", vec![], truth);
    let equality = engine.add_op("equal", vec![sort, sort], truth);
    engine.set_special(
        equality,
        SpecialOp::Equality {
            eq: true_term,
            neq: false_term,
        },
    );
    let wrap = engine.add_op("wrap", vec![sort], sort);
    let host = engine.add_op("host", vec![sort], sort);
    let hooks = ResolvedHostHooks::builder()
        .op("wrapSymbol", wrap)
        .build()
        .expect("resolved wrap hook");
    engine
        .bind_host_function(host, "gc.wrap-twice", hooks)
        .expect("bind allocating reducer");

    let argument = engine.make_const(constant);
    let redex = engine.make_free(host, vec![argument]);
    engine.set_gc_interval(Some(1));
    engine.set_trace(true);
    let result = engine
        .try_reduce(redex)
        .expect("GC-stressed host reduction");
    assert_eq!(engine.node(result).symbol(), wrap);
    let outer_child = engine
        .node(result)
        .children()
        .next()
        .expect("outer wrap child");
    assert_eq!(engine.node(outer_child).symbol(), wrap);
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(engine.rewrites(), 1);
    assert_eq!(
        engine.rewrite_breakdown(),
        (0, 0, 0, 0),
        "a host equation rewrite changes no semantic-driver subcount"
    );

    let trace = engine.take_trace();
    assert_eq!(trace.len(), 1);
    match &trace[0] {
        TraceEvent::Rewrite {
            kind,
            host_key: Some(key),
            redex: event_redex,
            result: event_result,
            ..
        } => {
            assert_eq!(*kind, RewriteKind::HostFunction);
            assert_eq!(key.as_str(), "gc.wrap-twice");
            assert_eq!(*event_redex, redex);
            assert_eq!(*event_result, result);
        }
        event => panic!("unexpected host trace event: {event:?}"),
    }

    engine.gc([result]);
    assert_eq!(engine.node(result).symbol(), wrap);
    let retained_child = engine
        .node(result)
        .children()
        .next()
        .expect("rooted result keeps its callback-built child");
    assert_eq!(engine.node(retained_child).symbol(), wrap);

    engine.set_gc_interval(None);
    engine.reset_rewrites();
    let left = engine.make_const(constant);
    let right = engine.make_const(constant);
    let built_in_redex = engine.make_free(equality, vec![left, right]);
    let built_in_result = engine
        .try_reduce(built_in_redex)
        .expect("ordinary built-in reduction");
    assert_eq!(engine.node(built_in_result).symbol(), true_term);
    let trace = engine.take_trace();
    assert_eq!(trace.len(), 1);
    assert!(matches!(
        trace[0],
        TraceEvent::Rewrite {
            kind: RewriteKind::BuiltIn,
            host_key: None,
            ..
        }
    ));
}

fn output_sort_fault(return_sort: ReturnSort) -> ReducerFault {
    let catalog = HostFunctionCatalog::builder()
        .register("sorts.bad-result", ReturnFirstArgument, unary_descriptor())
        .expect("register argument-returning reducer")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let top = engine.add_sort("Top");
    let expected = engine.add_sort("Expected");
    let sibling = engine.add_sort("Sibling");
    let other = engine.add_sort("Other");
    engine.add_subsort(expected, top);
    engine.add_subsort(sibling, top);
    engine.close_sorts();
    let bad_sort = match return_sort {
        ReturnSort::DifferentKind => other,
        ReturnSort::SameKindOutOfRange => sibling,
        ReturnSort::Error => {
            let kind = engine.sorts().kind_of(expected);
            engine.sorts().error_sort(kind)
        }
    };
    let bad_constant = engine.add_op("bad", vec![], bad_sort);
    let host = engine.add_op("host", vec![bad_sort], expected);
    engine
        .bind_host_function(host, "sorts.bad-result", no_hooks())
        .expect("bind argument-returning reducer");
    engine.set_trace(true);
    let argument = engine.make_const(bad_constant);
    let redex = engine.make_free(host, vec![argument]);
    let fault = engine
        .try_reduce(redex)
        .expect_err("invalid result must fault");
    assert_eq!(engine.rewrites(), 0, "fault is not a successful rewrite");
    assert!(
        engine.take_trace().is_empty(),
        "fault records no host event"
    );
    fault
}

#[derive(Clone, Copy)]
enum ReturnSort {
    DifferentKind,
    SameKindOutOfRange,
    Error,
}

#[test]
fn dispatcher_rejects_every_invalid_result_sort_class() {
    let different = output_sort_fault(ReturnSort::DifferentKind);
    assert_eq!(
        different.key().expect("fault key").as_str(),
        "sorts.bad-result"
    );
    assert!(
        different.message().contains("different kind"),
        "{different}"
    );

    let out_of_range = output_sort_fault(ReturnSort::SameKindOutOfRange);
    assert!(
        out_of_range.message().contains("not below selected range"),
        "{out_of_range}"
    );

    let error = output_sort_fault(ReturnSort::Error);
    assert!(error.message().contains("error sort"), "{error}");
}

fn faulting_identity_engine() -> (Engine, SymbolId) {
    let catalog = HostFunctionCatalog::builder()
        .register(
            "identity.fail",
            FaultReducer,
            StrictReducerDescriptor::builder(0).build(),
        )
        .expect("register identity fault reducer")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let sort = engine.add_sort("S");
    engine.close_sorts();
    let identity = engine.add_op("badIdentity", vec![], sort);
    engine
        .bind_host_function(identity, "identity.fail", no_hooks())
        .expect("bind identity reducer");
    let plus = engine.add_op_ac("plus", vec![sort, sort], sort, Some(identity));
    (engine, plus)
}

#[test]
fn identity_faults_cross_fallible_construction_and_panic_wrappers() {
    let (mut fallible, plus) = faulting_identity_engine();
    let fault = fallible
        .try_make_acu(plus, Vec::new())
        .expect_err("fallible ACU construction must return identity fault");
    assert_eq!(fault.key().expect("fault key").as_str(), "identity.fail");
    assert_eq!(fault.message(), "identity fault");

    let (mut infallible, plus) = faulting_identity_engine();
    let panic = catch_unwind(AssertUnwindSafe(|| infallible.make_acu(plus, Vec::new())))
        .expect_err("infallible constructor must panic on reducer fault");
    let message = panic
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| panic.downcast_ref::<&str>().copied())
        .unwrap_or("non-string panic");
    assert!(message.contains("identity.fail"), "{message}");
}

#[test]
fn binding_rejects_overloads_with_disjoint_result_kinds() {
    let catalog = HostFunctionCatalog::builder()
        .register(
            "binding.result-kinds",
            ReturnFirstArgument,
            unary_descriptor(),
        )
        .expect("register result-kind fixture")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let first_kind = engine.add_sort("FirstKind");
    let second_kind = engine.add_sort("SecondKind");
    engine.close_sorts();
    let host = engine.add_op("crossKindHost", vec![first_kind], first_kind);
    engine.add_op_decl(host, vec![second_kind], second_kind);

    let error = engine
        .bind_host_function(host, "binding.result-kinds", no_hooks())
        .expect_err("disjoint result kinds must reject strict binding");
    match error {
        HostBindingError::IncompatibleDeclarations(message) => {
            assert!(message.contains("`crossKindHost`"), "{message}");
            assert!(message.contains("different result kinds"), "{message}");
        }
        other => panic!("unexpected binding error: {other:?}"),
    }
}

#[test]
fn public_symbolic_normalization_seals_before_first_host_binding() {
    let catalog = HostFunctionCatalog::builder()
        .register("seal.symbolic", ReturnFirstArgument, unary_descriptor())
        .expect("register symbolic seal reducer")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let sort = engine.add_sort("S");
    engine.close_sorts();
    let value = engine.add_op("value", vec![], sort);
    let host = engine.add_op("host", vec![sort], sort);
    let value = engine.make_const(value);

    engine
        .try_normalize_for_unify(value)
        .expect("normalize a free constant");
    assert_eq!(
        engine.bind_host_function(host, "seal.symbolic", no_hooks()),
        Err(HostBindingError::SignatureSealed),
    );
}

#[test]
fn binding_is_one_way_and_semantic_execution_seals_signature() {
    let calls = Arc::new(AtomicUsize::new(0));
    let catalog = HostFunctionCatalog::builder()
        .register(
            "seal.reuse",
            ReuseReducer {
                calls: Arc::clone(&calls),
            },
            unary_descriptor(),
        )
        .expect("register seal reducer")
        .build();

    let mut late = Engine::with_host_functions(catalog.clone());
    let sort = late.add_sort("S");
    late.close_sorts();
    let a = late.add_op("a", vec![], sort);
    let host = late.add_op("host", vec![sort], sort);
    let root = late.make_const(a);
    late.try_reduce(root).expect("seal engine by reducing");
    assert_eq!(
        late.bind_host_function(host, "seal.reuse", no_hooks()),
        Err(HostBindingError::SignatureSealed)
    );

    let mut symbolic = Engine::with_host_functions(catalog.clone());
    let sort = symbolic.add_sort("S");
    symbolic.close_sorts();
    let a = symbolic.add_op("a", vec![], sort);
    let first = symbolic.add_op("first", vec![sort], sort);
    let second = symbolic.add_op("second", vec![sort], sort);
    symbolic
        .bind_host_function(first, "seal.reuse", no_hooks())
        .expect("bind first symbolic reducer");
    let root = symbolic.make_const(a);
    symbolic
        .try_normalize_for_unify(root)
        .expect("normalize a free constant");
    assert_eq!(
        symbolic.bind_host_function(second, "seal.reuse", no_hooks()),
        Err(HostBindingError::SignatureSealed)
    );

    let (mut bound, sort, _, host) = unary_engine(catalog, "seal.reuse");
    assert_eq!(
        bound.bind_host_function(host, "seal.reuse", no_hooks()),
        Err(HostBindingError::DuplicateBinding)
    );
    assert!(
        catch_unwind(AssertUnwindSafe(|| bound.set_strategy(host, &[1, 0]))).is_err(),
        "bound strategy is immutable"
    );
    assert!(
        catch_unwind(AssertUnwindSafe(|| bound.add_op_decl(
            host,
            vec![sort],
            sort
        )))
        .is_err(),
        "bound overload profile is immutable"
    );
    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            bound.set_special(host, SpecialOp::Branch { tests: Vec::new() })
        }))
        .is_err(),
        "bound special attachment is immutable"
    );
    assert!(
        catch_unwind(AssertUnwindSafe(|| bound.reserve_identity(host, sort))).is_err(),
        "bound theory/identity is immutable"
    );
}

#[test]
fn callback_panics_remain_trusted_panics_not_reducer_faults() {
    let catalog = HostFunctionCatalog::builder()
        .register("panic.trusted", PanicReducer, unary_descriptor())
        .expect("register panic reducer")
        .build();
    let (mut engine, _, constant, host) = unary_engine(catalog, "panic.trusted");
    let argument = engine.make_const(constant);
    let redex = engine.make_free(host, vec![argument]);
    let panic = catch_unwind(AssertUnwindSafe(|| engine.try_reduce(redex)))
        .expect_err("trusted callback panic must unwind");
    let message = panic
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| panic.downcast_ref::<&str>().copied())
        .unwrap_or("non-string panic");
    assert_eq!(message, "trusted reducer panic");
}

#[test]
fn host_binding_seal_rejects_equation_mutation_without_staling_cache() {
    let calls = Arc::new(AtomicUsize::new(0));
    let catalog = HostFunctionCatalog::builder()
        .register(
            "cache.decline",
            DeclineCounter {
                calls: Arc::clone(&calls),
            },
            unary_descriptor(),
        )
        .expect("register declining reducer")
        .build();
    let (mut engine, sort, a, host) = unary_engine(catalog, "cache.decline");
    let b = engine.add_op("b", vec![], sort);
    let argument = engine.make_const(a);
    let redex = engine.make_free(host, vec![argument]);

    assert_eq!(engine.try_reduce(redex).expect("initial decline"), redex);
    assert_eq!(engine.rewrites(), 0);
    assert_eq!(calls.load(Ordering::SeqCst), 1);

    assert!(
        catch_unwind(AssertUnwindSafe(|| {
            engine.add_equation(Equation {
                lhs: Term::op(host, vec![Term::constant(a)]),
                rhs: Term::constant(b),
                nr_vars: 0,
            });
        }))
        .is_err(),
        "equations cannot mutate a host-bound signature"
    );
    engine.reset_rewrites();
    assert_eq!(engine.try_reduce(redex).expect("cached decline"), redex);
    assert_eq!(engine.rewrites(), 0);
    assert_eq!(
        calls.load(Ordering::SeqCst),
        1,
        "rejected mutation leaves the current-epoch normal cache valid"
    );
}

#[test]
fn a_new_engine_can_resolve_the_same_key_to_a_new_implementation() {
    fn catalog(index: usize, calls: Arc<AtomicUsize>) -> HostFunctionCatalog {
        HostFunctionCatalog::builder()
            .register(
                "catalog.select",
                SelectArgument { index, calls },
                StrictReducerDescriptor::builder(2).build(),
            )
            .expect("register selector reducer")
            .build()
    }

    fn run(functions: HostFunctionCatalog, calls: &Arc<AtomicUsize>, expect_left: bool) {
        let mut engine = Engine::with_host_functions(functions);
        let sort = engine.add_sort("S");
        engine.close_sorts();
        let a = engine.add_op("a", vec![], sort);
        let b = engine.add_op("b", vec![], sort);
        let host = engine.add_op("host", vec![sort, sort], sort);
        engine
            .bind_host_function(host, "catalog.select", no_hooks())
            .expect("bind selector reducer");
        let left = engine.make_const(a);
        let right = engine.make_const(b);
        let redex = engine.make_free(host, vec![left, right]);
        let result = engine.try_reduce(redex).expect("selector reduction");
        assert_eq!(result == left, expect_left);
        assert_eq!(calls.load(Ordering::SeqCst), 1);
    }

    let first_calls = Arc::new(AtomicUsize::new(0));
    let second_calls = Arc::new(AtomicUsize::new(0));
    run(catalog(0, Arc::clone(&first_calls)), &first_calls, true);
    run(catalog(1, Arc::clone(&second_calls)), &second_calls, false);
}

#[test]
fn callback_arguments_follow_current_epoch_normal_forms() {
    let expected = Arc::new(Mutex::new(None));
    let calls = Arc::new(AtomicUsize::new(0));
    let catalog = HostFunctionCatalog::builder()
        .register(
            "normal.forward",
            ExpectTop {
                symbol: Arc::clone(&expected),
                calls: Arc::clone(&calls),
            },
            unary_descriptor(),
        )
        .expect("register forwarding observer")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let sort = engine.add_sort("S");
    engine.close_sorts();
    let a = engine.add_op("a", vec![], sort);
    let b = engine.add_op("b", vec![], sort);
    let c = engine.add_op("c", vec![], sort);
    let normalize = engine.add_op("normalize", vec![sort], sort);
    let host = engine.add_op("host", vec![sort], sort);
    engine.add_equation(Equation {
        lhs: Term::op(normalize, vec![Term::constant(a)]),
        rhs: Term::constant(b),
        nr_vars: 0,
    });
    *expected.lock().expect("expected-symbol lock") = Some(b);
    engine
        .bind_host_function(host, "normal.forward", no_hooks())
        .expect("bind forwarding observer");

    let a_dag = engine.make_const(a);
    let reducible = engine.make_free(normalize, vec![a_dag]);
    let normal = engine
        .try_reduce(reducible)
        .expect("normalize shared argument");
    assert_eq!(engine.node(normal).symbol(), b);
    let redex = engine.make_free(host, vec![reducible]);
    let result = engine
        .try_reduce(redex)
        .expect("strict callback over forwarded argument");
    assert_eq!(engine.node(result).symbol(), b);
    assert_eq!(calls.load(Ordering::SeqCst), 1);

    engine.add_equation(Equation {
        lhs: Term::constant(b),
        rhs: Term::constant(c),
        nr_vars: 0,
    });
    *expected.lock().expect("expected-symbol lock") = Some(c);
    let stale_forward_redex = engine.make_free(host, vec![reducible]);
    let revalidated = engine
        .try_reduce(stale_forward_redex)
        .expect("strict callback revalidates an old-epoch forwarded argument");
    assert_eq!(engine.node(revalidated).symbol(), c);
    assert_eq!(calls.load(Ordering::SeqCst), 2);
}

#[test]
fn free_host_receives_one_canonical_acu_argument() {
    let expected = Arc::new(Mutex::new(None));
    let calls = Arc::new(AtomicUsize::new(0));
    let catalog = HostFunctionCatalog::builder()
        .register(
            "normal.acu",
            InspectArgumentShape {
                expected: Arc::clone(&expected),
                calls: Arc::clone(&calls),
            },
            unary_descriptor(),
        )
        .expect("register ACU observer")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let sort = engine.add_sort("S");
    engine.close_sorts();
    let none = engine.add_op("none", vec![], sort);
    let a = engine.add_op("a", vec![], sort);
    let b = engine.add_op("b", vec![], sort);
    let plus = engine.add_op_ac("plus", vec![sort, sort], sort, Some(none));
    let host = engine.add_op("host", vec![sort], sort);
    *expected.lock().expect("expected-shape lock") = Some(ArgumentShape {
        root: plus,
        first_child: None,
        child_count: 2,
    });
    engine
        .bind_host_function(host, "normal.acu", no_hooks())
        .expect("bind ACU observer");

    let none_dag = engine.make_const(none);
    let a_dag = engine.make_const(a);
    let b_dag = engine.make_const(b);
    let argument = engine.make_acu(plus, vec![(b_dag, 1), (none_dag, 1), (a_dag, 1)]);
    assert_eq!(engine.node(argument).symbol(), plus);
    assert_eq!(engine.node(argument).children().count(), 2);
    let redex = engine.make_free(host, vec![argument]);
    let result = engine
        .try_reduce(redex)
        .expect("strict host over canonical ACU argument");
    assert_eq!(result, argument);
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(engine.rewrites(), 1);
}

#[test]
fn normal_lazy_argument_exposes_its_suspended_child_only_as_a_dag_ref() {
    let expected = Arc::new(Mutex::new(None));
    let calls = Arc::new(AtomicUsize::new(0));
    let catalog = HostFunctionCatalog::builder()
        .register(
            "normal.lazy-inner",
            InspectArgumentShape {
                expected: Arc::clone(&expected),
                calls: Arc::clone(&calls),
            },
            unary_descriptor(),
        )
        .expect("register lazy-inner observer")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let sort = engine.add_sort("S");
    engine.close_sorts();
    let a = engine.add_op("a", vec![], sort);
    let b = engine.add_op("b", vec![], sort);
    let normalize = engine.add_op("normalize", vec![sort], sort);
    let lazy = engine.add_op("lazy", vec![sort], sort);
    engine.set_strategy(lazy, &[0]);
    let host = engine.add_op("host", vec![sort], sort);
    engine.add_equation(Equation {
        lhs: Term::op(normalize, vec![Term::constant(a)]),
        rhs: Term::constant(b),
        nr_vars: 0,
    });
    *expected.lock().expect("expected-shape lock") = Some(ArgumentShape {
        root: lazy,
        first_child: Some(normalize),
        child_count: 1,
    });
    engine
        .bind_host_function(host, "normal.lazy-inner", no_hooks())
        .expect("bind lazy-inner observer");

    let a_dag = engine.make_const(a);
    let suspended = engine.make_free(normalize, vec![a_dag]);
    let argument = engine.make_free(lazy, vec![suspended]);
    let redex = engine.make_free(host, vec![argument]);
    let result = engine
        .try_reduce(redex)
        .expect("strict host over normal lazy argument");
    assert_eq!(engine.node(result).symbol(), lazy);
    let child = engine
        .node(result)
        .children()
        .next()
        .expect("lazy result child");
    assert_eq!(engine.node(child).symbol(), normalize);
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(engine.rewrites(), 1);
}

#[test]
fn decline_falls_through_to_an_ordinary_equation() {
    let calls = Arc::new(AtomicUsize::new(0));
    let catalog = HostFunctionCatalog::builder()
        .register(
            "decline.ordinary",
            DeclineCounter {
                calls: Arc::clone(&calls),
            },
            unary_descriptor(),
        )
        .expect("register declining reducer")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let sort = engine.add_sort("S");
    engine.close_sorts();
    let a = engine.add_op("a", vec![], sort);
    let b = engine.add_op("b", vec![], sort);
    let host = engine.add_op("host", vec![sort], sort);
    engine.add_equation(Equation {
        lhs: Term::op(host, vec![Term::constant(a)]),
        rhs: Term::constant(b),
        nr_vars: 0,
    });
    engine
        .bind_host_function(host, "decline.ordinary", no_hooks())
        .expect("bind declining reducer");

    let argument = engine.make_const(a);
    let redex = engine.make_free(host, vec![argument]);
    let result = engine
        .try_reduce(redex)
        .expect("ordinary equation after host decline");
    assert_eq!(engine.node(result).symbol(), b);
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(engine.rewrites(), 1);
}

#[test]
fn callback_theory_construction_propagates_identity_reducer_faults() {
    let build_descriptor = StrictReducerDescriptor::builder(0)
        .require_op_hook(
            "plusSymbol",
            &[HookSort::Result, HookSort::Result],
            HookSort::Result,
        )
        .require_constant_term_hook("identityTerm", HookSort::Result)
        .build();
    let catalog = HostFunctionCatalog::builder()
        .register(
            "identity.fail",
            FaultReducer,
            StrictReducerDescriptor::builder(0).build(),
        )
        .expect("register identity fault reducer")
        .register("identity.construct", BuildThroughIdentity, build_descriptor)
        .expect("register theory constructor")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let sort = engine.add_sort("S");
    engine.close_sorts();
    let bad_identity = engine.add_op("badIdentity", vec![], sort);
    let plus = engine.add_op_ac("plus", vec![sort, sort], sort, Some(bad_identity));
    let construct = engine.add_op("construct", vec![], sort);
    engine
        .bind_host_function(bad_identity, "identity.fail", no_hooks())
        .expect("bind identity fault");
    let hooks = ResolvedHostHooks::builder()
        .op("plusSymbol", plus)
        .constant_term("identityTerm", bad_identity)
        .build()
        .expect("resolved construction hooks");
    engine
        .bind_host_function(construct, "identity.construct", hooks)
        .expect("bind theory constructor");
    engine.set_trace(true);

    let root = engine.make_const(construct);
    let fault = engine
        .try_reduce(root)
        .expect_err("identity fault must escape callback construction");
    assert_eq!(fault.key().expect("fault key").as_str(), "identity.fail");
    assert_eq!(fault.message(), "identity fault");
    assert_eq!(engine.rewrites(), 0);
    assert!(engine.take_trace().is_empty());
}

#[test]
fn callback_theory_construction_returns_canonical_acu_au_and_cui_results() {
    let domain = [HookSort::Result, HookSort::Result];
    let descriptor = StrictReducerDescriptor::builder(0)
        .require_op_hook("acuSymbol", &domain, HookSort::Result)
        .require_op_hook("auSymbol", &domain, HookSort::Result)
        .require_op_hook("cuiSymbol", &domain, HookSort::Result)
        .require_constant_term_hook("identityTerm", HookSort::Result)
        .require_constant_term_hook("valueTerm", HookSort::Result)
        .build();
    let catalog = HostFunctionCatalog::builder()
        .register("theory.canonical", BuildCanonicalTheories, descriptor)
        .expect("register canonical theory constructor")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let sort = engine.add_sort("S");
    engine.close_sorts();
    let none = engine.add_op("none", vec![], sort);
    let value = engine.add_op("value", vec![], sort);
    let acu = engine.add_op_ac("acu", vec![sort, sort], sort, Some(none));
    let au = engine.add_op_au("au", vec![sort, sort], sort, Some(none));
    let cui = engine.add_op_cui("cui", vec![sort, sort], sort, true, true, Some(none));
    let construct = engine.add_op("construct", vec![], sort);
    let hooks = ResolvedHostHooks::builder()
        .op("acuSymbol", acu)
        .op("auSymbol", au)
        .op("cuiSymbol", cui)
        .constant_term("identityTerm", none)
        .constant_term("valueTerm", value)
        .build()
        .expect("resolve canonical construction hooks");
    engine
        .bind_host_function(construct, "theory.canonical", hooks)
        .expect("bind canonical theory constructor");
    engine.set_gc_interval(Some(1));

    let root = engine.make_const(construct);
    let result = engine
        .try_reduce(root)
        .expect("GC-stressed canonical theory construction");
    assert_eq!(engine.node(result).symbol(), value);
    assert_eq!(engine.rewrites(), 1);
}

#[test]
fn callback_builder_rejects_wrong_argument_sorts() {
    let descriptor = StrictReducerDescriptor::builder(1)
        .require_op_hook("resultSymbol", &[HookSort::Result], HookSort::Result)
        .build();
    let catalog = HostFunctionCatalog::builder()
        .register("builder.wrong-sort", BuildOnce, descriptor)
        .expect("register wrong-sort builder")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let input = engine.add_sort("Input");
    let output = engine.add_sort("Output");
    engine.close_sorts();
    let argument_symbol = engine.add_op("argument", vec![], input);
    let result_symbol = engine.add_op("result", vec![output], output);
    let host = engine.add_op("host", vec![input], output);
    let hooks = ResolvedHostHooks::builder()
        .op("resultSymbol", result_symbol)
        .build()
        .expect("resolve result hook");
    engine
        .bind_host_function(host, "builder.wrong-sort", hooks)
        .expect("bind wrong-sort builder");
    let argument = engine.make_const(argument_symbol);
    let root = engine.make_free(host, vec![argument]);
    let fault = engine
        .try_reduce(root)
        .expect_err("wrong-sort callback construction must fail");
    assert_eq!(
        fault.key().expect("fault key").as_str(),
        "builder.wrong-sort"
    );
    assert!(
        fault
            .message()
            .contains("no declaration of `result` accepts the supplied argument sorts"),
        "{fault}"
    );
}

#[test]
fn active_hook_view_builds_with_callback_scoped_symbols() {
    let descriptor = StrictReducerDescriptor::builder(1)
        .require_op_hook("wrapperSymbol", &[HookSort::Result], HookSort::Result)
        .require_constant_term_hook("constantTerm", HookSort::Argument(0))
        .build();
    let catalog = HostFunctionCatalog::builder()
        .register("hooks.active", ActiveHookUse, descriptor)
        .expect("register active-hook reducer")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let sort = engine.add_sort("S");
    engine.close_sorts();
    let constant = engine.add_op("constant", vec![], sort);
    let wrapper = engine.add_op("wrapper", vec![sort], sort);
    let host = engine.add_op("host", vec![sort], sort);
    let hooks = ResolvedHostHooks::builder()
        .op("wrapperSymbol", wrapper)
        .constant_term("constantTerm", constant)
        .build()
        .expect("resolve active hooks");
    engine
        .bind_host_function(host, "hooks.active", hooks)
        .expect("bind active-hook reducer");

    let argument = engine.make_const(constant);
    let root = engine.make_free(host, vec![argument]);
    let result = engine.try_reduce(root).expect("build through active hooks");
    assert_eq!(engine.node(result).symbol(), wrapper);
    let child = engine
        .node(result)
        .children()
        .next()
        .expect("wrapper child");
    assert_eq!(engine.node(child).symbol(), constant);
    assert_eq!(engine.rewrites(), 1);
}

#[test]
fn returned_reducible_term_restarts_ordinary_normalization() {
    let descriptor = StrictReducerDescriptor::builder(1)
        .require_op_hook("resultSymbol", &[HookSort::Argument(0)], HookSort::Result)
        .build();
    let catalog = HostFunctionCatalog::builder()
        .register("result.reducible", BuildOnce, descriptor)
        .expect("register result builder")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let sort = engine.add_sort("S");
    engine.close_sorts();
    let a = engine.add_op("a", vec![], sort);
    let b = engine.add_op("b", vec![], sort);
    let simplify = engine.add_op("simplify", vec![sort], sort);
    let host = engine.add_op("host", vec![sort], sort);
    engine.add_equation(Equation {
        lhs: Term::op(simplify, vec![Term::constant(a)]),
        rhs: Term::constant(b),
        nr_vars: 0,
    });
    let hooks = ResolvedHostHooks::builder()
        .op("resultSymbol", simplify)
        .build()
        .expect("resolved result hook");
    engine
        .bind_host_function(host, "result.reducible", hooks)
        .expect("bind result builder");
    engine.set_trace(true);

    let argument = engine.make_const(a);
    let root = engine.make_free(host, vec![argument]);
    let result = engine.try_reduce(root).expect("normalize callback result");
    assert_eq!(engine.node(result).symbol(), b);
    assert_eq!(engine.rewrites(), 2);
    let events = engine.take_trace();
    assert_eq!(events.len(), 2);
    assert!(matches!(
        &events[0],
        TraceEvent::Rewrite {
            kind: RewriteKind::HostFunction,
            host_key: Some(key),
            ..
        } if key.as_str() == "result.reducible"
    ));
    assert!(matches!(
        events[1],
        TraceEvent::Rewrite {
            kind: RewriteKind::Equation,
            ..
        }
    ));
}

#[test]
fn typed_adapters_survive_collection_at_every_callback_allocation() {
    fn uppercase(input: &[u8]) -> Vec<u8> {
        input.iter().map(u8::to_ascii_uppercase).collect()
    }
    fn concatenate(left: &[u8], right: &[u8]) -> Vec<u8> {
        [left, right].concat()
    }
    let unary_input_ptr = Arc::new(AtomicUsize::new(0));
    let unary_observer = Arc::clone(&unary_input_ptr);
    let left_input_ptr = Arc::new(AtomicUsize::new(0));
    let right_input_ptr = Arc::new(AtomicUsize::new(0));
    let left_observer = Arc::clone(&left_input_ptr);
    let right_observer = Arc::clone(&right_input_ptr);

    let catalog = HostFunctionCatalog::builder()
        .register_typed1(
            "typed.uppercase",
            codecs::string(),
            codecs::string(),
            move |input| {
                unary_observer.store(input.as_ptr() as usize, Ordering::SeqCst);
                uppercase(input)
            },
        )
        .expect("register typed unary reducer")
        .register_typed2(
            "typed.concatenate",
            codecs::string(),
            codecs::string(),
            codecs::string(),
            move |left, right| {
                left_observer.store(left.as_ptr() as usize, Ordering::SeqCst);
                right_observer.store(right.as_ptr() as usize, Ordering::SeqCst);
                concatenate(left, right)
            },
        )
        .expect("register typed binary reducer")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let string = engine.add_sort("String");
    engine.close_sorts();
    let marker = engine.add_op("<Strings>", vec![], string);
    engine.set_symbol_class(marker, SymbolClass::Marker);
    let unary = engine.add_op("uppercase", vec![string], string);
    let binary = engine.add_op("concatenate", vec![string, string], string);
    let hooks = || {
        ResolvedHostHooks::builder()
            .op("stringSymbol", marker)
            .build()
            .expect("resolved string hook")
    };
    engine
        .bind_host_function(unary, "typed.uppercase", hooks())
        .expect("bind typed unary reducer");
    engine
        .bind_host_function(binary, "typed.concatenate", hooks())
        .expect("bind typed binary reducer");
    engine.set_gc_interval(Some(1));

    let lower = engine.make_string(marker, b"host");
    let lower_ptr = match engine.node(lower).repr() {
        NodeRepr::Str(value) => value.as_ptr() as usize,
        repr => panic!("unexpected typed unary input: {repr:?}"),
    };
    let unary_root = engine.make_free(unary, vec![lower]);
    let upper = engine
        .try_reduce(unary_root)
        .expect("GC-stressed typed unary reduction");
    match engine.node(upper).repr() {
        NodeRepr::Str(value) => assert_eq!(value, b"HOST"),
        repr => panic!("unexpected typed unary result: {repr:?}"),
    }
    assert_eq!(engine.rewrites(), 1);
    assert_eq!(
        unary_input_ptr.load(Ordering::SeqCst),
        lower_ptr,
        "typed unary decoding copied its native byte-string input"
    );

    engine.reset_rewrites();
    let left = engine.make_string(marker, b"safe");
    let right = engine.make_string(marker, b"-gc");
    let left_ptr = match engine.node(left).repr() {
        NodeRepr::Str(value) => value.as_ptr() as usize,
        repr => panic!("unexpected typed binary left input: {repr:?}"),
    };
    let right_ptr = match engine.node(right).repr() {
        NodeRepr::Str(value) => value.as_ptr() as usize,
        repr => panic!("unexpected typed binary right input: {repr:?}"),
    };
    let binary_root = engine.make_free(binary, vec![left, right]);
    let joined = engine
        .try_reduce(binary_root)
        .expect("GC-stressed typed binary reduction");
    match engine.node(joined).repr() {
        NodeRepr::Str(value) => assert_eq!(value, b"safe-gc"),
        repr => panic!("unexpected typed binary result: {repr:?}"),
    }
    assert_eq!(engine.rewrites(), 1);
    assert_eq!(
        left_input_ptr.load(Ordering::SeqCst),
        left_ptr,
        "typed binary decoding copied its left native byte-string input"
    );
    assert_eq!(
        right_input_ptr.load(Ordering::SeqCst),
        right_ptr,
        "typed binary decoding copied its right native byte-string input"
    );
}

#[derive(Clone)]
struct CountedFaultReducer {
    calls: Arc<AtomicUsize>,
    message: &'static str,
}

impl StrictReducer for CountedFaultReducer {
    fn reduce<'ctx>(
        &self,
        _ctx: &mut StrictReduceCtx<'ctx>,
        _call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        self.calls.fetch_add(1, Ordering::SeqCst);
        Err(ReducerFault::new(self.message))
    }
}

#[derive(Clone, Copy)]
struct IdentityToNone;

impl StrictReducer for IdentityToNone {
    fn reduce<'ctx>(
        &self,
        ctx: &mut StrictReduceCtx<'ctx>,
        call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        Ok(StrictOutcome::Reduced(
            ctx.constant(call.hooks().term_symbol("noneTerm"))?,
        ))
    }
}

#[derive(Clone, Copy)]
struct DuplicateArgument;

impl StrictReducer for DuplicateArgument {
    fn reduce<'ctx>(
        &self,
        ctx: &mut StrictReduceCtx<'ctx>,
        call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        let plus = call.hooks().op_symbol("plusSymbol");
        let argument = call.argument(0).as_ref();
        Ok(StrictOutcome::Reduced(
            ctx.app(plus, &[argument, argument])?,
        ))
    }
}

#[derive(Clone, Copy)]
enum AllocatingOutcome {
    Reduced,
    Decline,
    Fault,
    Panic,
}

#[derive(Clone, Copy)]
struct AllocateTemporary {
    outcome: AllocatingOutcome,
}

impl StrictReducer for AllocateTemporary {
    fn reduce<'ctx>(
        &self,
        ctx: &mut StrictReduceCtx<'ctx>,
        call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        let _temporary = ctx.constant(call.hooks().term_symbol("temporaryTerm"))?;
        match self.outcome {
            AllocatingOutcome::Reduced => Ok(StrictOutcome::Reduced(
                ctx.constant(call.hooks().term_symbol("resultTerm"))?,
            )),
            AllocatingOutcome::Decline => Ok(StrictOutcome::Decline),
            AllocatingOutcome::Fault => Err(ReducerFault::new("allocated fault")),
            AllocatingOutcome::Panic => panic!("allocated panic"),
        }
    }
}

fn assert_fault(fault: &ReducerFault, key: &str, message: &str) {
    assert_eq!(fault.key().expect("fault key").as_str(), key);
    assert_eq!(fault.message(), message);
}

fn assert_reducer_panic(panic: Box<dyn std::any::Any + Send>, key: &str, message: &str) {
    let actual = panic
        .downcast_ref::<String>()
        .map(String::as_str)
        .or_else(|| panic.downcast_ref::<&str>().copied())
        .unwrap_or("non-string panic");
    assert_eq!(actual, format!("strict reducer `{key}` failed: {message}"));
}

fn assert_no_semantic_effects(engine: &mut Engine) {
    assert_eq!(engine.rewrites(), 0);
    assert_eq!(engine.rewrite_breakdown(), (0, 0, 0, 0));
    assert!(engine.take_trace().is_empty());
}

fn allocating_descriptor() -> StrictReducerDescriptor {
    StrictReducerDescriptor::builder(0)
        .require_constant_term_hook("temporaryTerm", HookSort::Result)
        .require_constant_term_hook("resultTerm", HookSort::Result)
        .build()
}

fn allocating_hooks(temporary: SymbolId, result: SymbolId) -> ResolvedHostHooks {
    ResolvedHostHooks::builder()
        .constant_term("temporaryTerm", temporary)
        .constant_term("resultTerm", result)
        .build()
        .expect("allocation hooks")
}

#[test]
fn callback_acu_identity_materialization_roots_outer_scope_across_nested_gc() {
    let identity_descriptor = StrictReducerDescriptor::builder(0)
        .require_constant_term_hook("noneTerm", HookSort::Result)
        .build();
    let duplicate_descriptor = StrictReducerDescriptor::builder(1)
        .require_op_hook(
            "plusSymbol",
            &[HookSort::Argument(0), HookSort::Argument(0)],
            HookSort::Result,
        )
        .build();
    let catalog = HostFunctionCatalog::builder()
        .register("identity.none", IdentityToNone, identity_descriptor)
        .expect("register identity reducer")
        .register(
            "callback.duplicate",
            DuplicateArgument,
            duplicate_descriptor,
        )
        .expect("register outer reducer")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let sort = engine.add_sort("S");
    engine.close_sorts();
    let none = engine.add_op("none", vec![], sort);
    let identity_host = engine.add_op("identityHost", vec![], sort);
    let value = engine.add_op("value", vec![], sort);
    let plus = engine.add_op_ac("plus", vec![sort, sort], sort, Some(identity_host));
    let outer = engine.add_op("outer", vec![sort], sort);
    engine
        .bind_host_function(
            identity_host,
            "identity.none",
            ResolvedHostHooks::builder()
                .constant_term("noneTerm", none)
                .build()
                .expect("identity hooks"),
        )
        .expect("bind identity reducer");
    engine
        .bind_host_function(
            outer,
            "callback.duplicate",
            ResolvedHostHooks::builder()
                .op("plusSymbol", plus)
                .build()
                .expect("outer hooks"),
        )
        .expect("bind outer reducer");

    let argument = engine.make_const(value);
    let redex = engine.make_free(outer, vec![argument]);
    engine.set_gc_interval(Some(1));
    let result = engine
        .try_reduce(redex)
        .expect("nested identity reduction under callback GC");

    assert_eq!(engine.node(result).symbol(), plus);
    assert_eq!(
        engine.node(result).children().collect::<Vec<_>>(),
        vec![argument, argument]
    );
    assert_eq!(
        engine.rewrites(),
        1,
        "identity DAG preparation is maintenance; only the outer host step is user accounting"
    );

    engine.gc([result]);
    assert_eq!(engine.node(result).symbol(), plus);
    assert_eq!(
        engine.node(result).children().collect::<Vec<_>>(),
        vec![argument, argument],
        "the returned canonical DAG transitively retains the original callback argument"
    );
}

#[test]
fn callback_scope_roots_are_released_for_every_callback_exit() {
    let catalog = HostFunctionCatalog::builder()
        .register(
            "scope.reduced",
            AllocateTemporary {
                outcome: AllocatingOutcome::Reduced,
            },
            allocating_descriptor(),
        )
        .expect("register reduced allocator")
        .register(
            "scope.decline",
            AllocateTemporary {
                outcome: AllocatingOutcome::Decline,
            },
            allocating_descriptor(),
        )
        .expect("register declining allocator")
        .register(
            "scope.fault",
            AllocateTemporary {
                outcome: AllocatingOutcome::Fault,
            },
            allocating_descriptor(),
        )
        .expect("register faulting allocator")
        .register(
            "scope.panic",
            AllocateTemporary {
                outcome: AllocatingOutcome::Panic,
            },
            allocating_descriptor(),
        )
        .expect("register panicking allocator")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let sort = engine.add_sort("S");
    engine.close_sorts();
    let temporary = engine.add_op("temporary", vec![], sort);
    let returned = engine.add_op("returned", vec![], sort);
    let reduced_host = engine.add_op("reducedHost", vec![], sort);
    let decline_host = engine.add_op("declineHost", vec![], sort);
    let fault_host = engine.add_op("faultHost", vec![], sort);
    let panic_host = engine.add_op("panicHost", vec![], sort);
    for (host, key) in [
        (reduced_host, "scope.reduced"),
        (decline_host, "scope.decline"),
        (fault_host, "scope.fault"),
        (panic_host, "scope.panic"),
    ] {
        engine
            .bind_host_function(host, key, allocating_hooks(temporary, returned))
            .expect("bind allocating reducer");
    }
    engine.set_gc_interval(Some(u64::MAX));

    let mut retained = Vec::new();

    let reduced_redex = engine.make_const(reduced_host);
    let result = engine
        .try_reduce(reduced_redex)
        .expect("reduced callback outcome");
    retained.extend([reduced_redex, result]);
    assert_eq!(
        engine.gc(retained.iter().copied()),
        1,
        "the unreturned temporary is reclaimed after a successful callback"
    );
    assert_eq!(engine.node(result).symbol(), returned);

    let decline_redex = engine.make_const(decline_host);
    assert_eq!(
        engine
            .try_reduce(decline_redex)
            .expect("declining callback outcome"),
        decline_redex
    );
    retained.push(decline_redex);
    assert_eq!(
        engine.gc(retained.iter().copied()),
        1,
        "the unreturned temporary is reclaimed after Decline"
    );

    let fault_redex = engine.make_const(fault_host);
    let fault = engine
        .try_reduce(fault_redex)
        .expect_err("faulting callback outcome");
    assert_fault(&fault, "scope.fault", "allocated fault");
    retained.push(fault_redex);
    assert_eq!(
        engine.gc(retained.iter().copied()),
        1,
        "the unreturned temporary is reclaimed after a reducer fault"
    );

    let panic_redex = engine.make_const(panic_host);
    catch_unwind(AssertUnwindSafe(|| engine.try_reduce(panic_redex)))
        .expect_err("trusted callback panic");
    retained.push(panic_redex);
    assert_eq!(
        engine.gc(retained.iter().copied()),
        1,
        "the unreturned temporary is reclaimed while unwinding a callback panic"
    );
    assert_eq!(engine.node(result).symbol(), returned);
}

#[test]
fn faulting_membership_stops_before_later_candidate_and_restores_state() {
    let calls = Arc::new(AtomicUsize::new(0));
    let catalog = HostFunctionCatalog::builder()
        .register(
            "membership.fail",
            CountedFaultReducer {
                calls: Arc::clone(&calls),
                message: "membership fault",
            },
            StrictReducerDescriptor::builder(0).build(),
        )
        .expect("register membership fault reducer")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let smaller = engine.add_sort("Smaller");
    let top = engine.add_sort("Top");
    engine.add_subsort(smaller, top);
    engine.close_sorts();
    let subject = engine.add_op("subject", vec![], top);
    let expected = engine.add_op("expected", vec![], top);
    let faulting = engine.add_op("faulting", vec![], top);
    engine
        .bind_host_function(faulting, "membership.fail", no_hooks())
        .expect("bind membership fault reducer");
    engine.add_conditional_membership(
        Term::constant(subject),
        smaller,
        0,
        vec![ConditionFragment::Equality {
            lhs: Term::constant(faulting),
            rhs: Term::constant(expected),
        }],
    );
    engine.add_membership(Membership {
        lhs: Term::constant(subject),
        sort: smaller,
        nr_vars: 0,
    });

    let root = engine.make_const(subject);
    engine.set_trace(true);
    let fault = engine
        .try_reduce(root)
        .expect_err("conditional membership reducer fault");
    assert_fault(&fault, "membership.fail", "membership fault");
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(
        engine.node(root).sort(),
        top,
        "the later unconditional membership must not lower the subject"
    );
    assert_no_semantic_effects(&mut engine);
}

#[test]
fn search_initial_goal_fault_is_terminal_and_replayed_without_resume() {
    let calls = Arc::new(AtomicUsize::new(0));
    let catalog = HostFunctionCatalog::builder()
        .register(
            "search.initial-fail",
            CountedFaultReducer {
                calls: Arc::clone(&calls),
                message: "initial goal fault",
            },
            StrictReducerDescriptor::builder(0).build(),
        )
        .expect("register initial-goal fault reducer")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let sort = engine.add_sort("S");
    engine.close_sorts();
    let initial = engine.add_op("initial", vec![], sort);
    let faulting = engine.add_op("faulting", vec![], sort);
    engine
        .bind_host_function(faulting, "search.initial-fail", no_hooks())
        .expect("bind initial-goal fault reducer");
    engine.set_trace(true);

    let initial_dag = engine.make_const(initial);
    let mut search = engine
        .try_search(
            initial_dag,
            Term::constant(initial),
            0,
            vec![ConditionFragment::Equality {
                lhs: Term::constant(faulting),
                rhs: Term::constant(initial),
            }],
            Arrow::Star,
            None,
        )
        .expect("construct search");
    let first = search
        .try_next_solution(&mut engine)
        .expect_err("initial goal fault");
    let second = search
        .try_next_solution(&mut engine)
        .expect_err("terminal search repeats its fault");
    assert_eq!(first, second);
    assert_fault(&first, "search.initial-fail", "initial goal fault");
    let panic = catch_unwind(AssertUnwindSafe(|| search.next_solution(&mut engine)))
        .expect_err("infallible Search boundary must panic on the stored reducer fault");
    assert_reducer_panic(panic, "search.initial-fail", "initial goal fault");
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(search.states(), 1);
    assert_no_semantic_effects(&mut engine);
}

#[test]
fn search_successor_fault_discards_later_raw_successors() {
    let calls = Arc::new(AtomicUsize::new(0));
    let catalog = HostFunctionCatalog::builder()
        .register(
            "search.successor-fail",
            CountedFaultReducer {
                calls: Arc::clone(&calls),
                message: "successor fault",
            },
            StrictReducerDescriptor::builder(0).build(),
        )
        .expect("register successor fault reducer")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let sort = engine.add_sort("S");
    engine.close_sorts();
    let initial = engine.add_op("initial", vec![], sort);
    let good = engine.add_op("good", vec![], sort);
    let goal = engine.add_op("goal", vec![], sort);
    let later = engine.add_op("later", vec![], sort);
    let faulting = engine.add_op("faulting", vec![], sort);
    engine
        .bind_host_function(faulting, "search.successor-fail", no_hooks())
        .expect("bind successor fault reducer");
    engine.add_rule(Term::constant(initial), Term::constant(good), 0);
    engine.add_rule(Term::constant(initial), Term::constant(faulting), 0);
    engine.add_rule(Term::constant(initial), Term::constant(later), 0);
    engine.set_trace(true);

    let initial_dag = engine.make_const(initial);
    let mut search = engine
        .try_search(
            initial_dag,
            Term::constant(goal),
            0,
            Vec::new(),
            Arrow::Plus,
            None,
        )
        .expect("construct successor search");
    let states_before = search.states();
    let graph_before = search.graph();
    let first = search
        .try_next_solution(&mut engine)
        .expect_err("first successor faults");
    let second = search
        .try_next_solution(&mut engine)
        .expect_err("search must not resume at the later successor");
    assert_eq!(first, second);
    assert_fault(&first, "search.successor-fail", "successor fault");
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(search.states(), states_before);
    assert_eq!(
        search.graph(),
        graph_before,
        "a state and arc committed before the later fault must be rolled back"
    );
    assert!(search.state_term(1).is_none());
    assert_no_semantic_effects(&mut engine);
}

#[test]
fn position_fair_rewriting_fault_clears_cursor_and_is_terminal() {
    let calls = Arc::new(AtomicUsize::new(0));
    let catalog = HostFunctionCatalog::builder()
        .register(
            "frewrite.fail",
            CountedFaultReducer {
                calls: Arc::clone(&calls),
                message: "frewrite fault",
            },
            StrictReducerDescriptor::builder(0).build(),
        )
        .expect("register frewrite fault reducer")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let sort = engine.add_sort("S");
    engine.close_sorts();
    let initial = engine.add_op("initial", vec![], sort);
    let later = engine.add_op("later", vec![], sort);
    let faulting = engine.add_op("faulting", vec![], sort);
    engine
        .bind_host_function(faulting, "frewrite.fail", no_hooks())
        .expect("bind frewrite fault reducer");
    engine.add_rule(Term::constant(initial), Term::constant(faulting), 0);
    engine.add_rule(Term::constant(initial), Term::constant(later), 0);
    engine.set_trace(true);

    let initial_dag = engine.make_const(initial);
    let mut rewriting = engine.frewrite(initial_dag, 1);
    let first = rewriting
        .try_run(&mut engine, None)
        .expect_err("first position-fair candidate faults");
    let second = rewriting
        .try_run(&mut engine, None)
        .expect_err("position-fair session must not advance to the later rule");
    assert_eq!(first, second);
    assert_fault(&first, "frewrite.fail", "frewrite fault");
    let panic = catch_unwind(AssertUnwindSafe(|| rewriting.run(&mut engine, None)))
        .expect_err("infallible Rewriting boundary must panic on the stored reducer fault");
    assert_reducer_panic(panic, "frewrite.fail", "frewrite fault");
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(rewriting.current(), initial_dag);
    assert_no_semantic_effects(&mut engine);
}

#[test]
fn identical_faulting_redex_is_not_cached_as_a_normal_form() {
    let calls = Arc::new(AtomicUsize::new(0));
    let catalog = HostFunctionCatalog::builder()
        .register(
            "fault.retry",
            CountedFaultReducer {
                calls: Arc::clone(&calls),
                message: "retry fault",
            },
            StrictReducerDescriptor::builder(0).build(),
        )
        .expect("register retry fault reducer")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let sort = engine.add_sort("S");
    engine.close_sorts();
    let faulting = engine.add_op("faulting", vec![], sort);
    engine
        .bind_host_function(faulting, "fault.retry", no_hooks())
        .expect("bind retry fault reducer");
    engine.set_trace(true);

    let redex = engine.make_const(faulting);
    let first = engine
        .try_reduce(redex)
        .expect_err("first reduction faults");
    let second = engine
        .try_reduce(redex)
        .expect_err("the identical redex dispatches the reducer again");
    assert_eq!(first, second);
    assert_fault(&first, "fault.retry", "retry fault");
    let panic = catch_unwind(AssertUnwindSafe(|| engine.reduce(redex)))
        .expect_err("infallible Engine boundary must panic on the reducer fault");
    assert_reducer_panic(panic, "fault.retry", "retry fault");
    assert_eq!(calls.load(Ordering::SeqCst), 3);
    assert_no_semantic_effects(&mut engine);
}

#[test]
fn rule_fair_rewriting_fault_is_terminal_on_repeat_call() {
    let calls = Arc::new(AtomicUsize::new(0));
    let catalog = HostFunctionCatalog::builder()
        .register(
            "rewrite.fail",
            CountedFaultReducer {
                calls: Arc::clone(&calls),
                message: "rewrite fault",
            },
            StrictReducerDescriptor::builder(0).build(),
        )
        .expect("register rewrite fault reducer")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let sort = engine.add_sort("S");
    engine.close_sorts();
    let initial = engine.add_op("initial", vec![], sort);
    let later = engine.add_op("later", vec![], sort);
    let faulting = engine.add_op("faulting", vec![], sort);
    engine
        .bind_host_function(faulting, "rewrite.fail", no_hooks())
        .expect("bind rewrite fault reducer");
    engine.add_rule(Term::constant(initial), Term::constant(faulting), 0);
    engine.add_rule(Term::constant(initial), Term::constant(later), 0);
    engine.set_trace(true);

    let initial_dag = engine.make_const(initial);
    let mut rewriting = engine.rewrite(initial_dag);
    let first = rewriting
        .try_run(&mut engine, None)
        .expect_err("first rule-fair candidate faults");
    let second = rewriting
        .try_run(&mut engine, None)
        .expect_err("rule-fair session must not advance to the later rule");
    assert_eq!(first, second);
    assert_fault(&first, "rewrite.fail", "rewrite fault");
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(rewriting.current(), initial_dag);
    assert_no_semantic_effects(&mut engine);
}

/// Decode a numeral that a `counter` special yields: the zero constant or a compact `s^n(0)`.
fn counter_numeral(engine: &Engine, id: DagId, zero: SymbolId) -> String {
    match engine.node(id).repr() {
        NodeRepr::Iter { count, .. } => count,
        NodeRepr::App if engine.node(id).symbol() == zero => "0".to_string(),
        _ => panic!("counter result is not a numeral"),
    }
}

/// A reducer fault rolls back every `counter` operator to its value at the start of the faulted
/// rule-fair or position-fair drive. Both operators fire before the fault. Each has its own
/// sequence, so a later drive, started without `reset_counter`, yields 0 for both again.
#[test]
fn rewriting_fault_restores_every_counter_operator() {
    for position_fair in [false, true] {
        let calls = Arc::new(AtomicUsize::new(0));
        let catalog = HostFunctionCatalog::builder()
            .register(
                "counter.fail",
                CountedFaultReducer {
                    calls: Arc::clone(&calls),
                    message: "counter fault",
                },
                StrictReducerDescriptor::builder(0).build(),
            )
            .expect("register counter fault reducer")
            .build();
        let mut engine = Engine::with_host_functions(catalog);
        let zero_sort = engine.add_sort("Zero");
        let nz_nat = engine.add_sort("NzNat");
        let nat = engine.add_sort("Nat");
        let state = engine.add_sort("State");
        engine.add_subsort(zero_sort, nat);
        engine.add_subsort(nz_nat, nat);
        engine.close_sorts();
        let zero = engine.add_op("0", vec![], zero_sort);
        let succ = engine.add_op_iter("s", vec![nat], nz_nat);
        let nat_hooks = NatHooks {
            succ,
            zero,
            minus: None,
        };
        let tick = engine.add_op("tick", vec![], nat);
        let tock = engine.add_op("tock", vec![], nat);
        engine.set_special(tick, SpecialOp::Counter { nat: nat_hooks });
        engine.set_special(tock, SpecialOp::Counter { nat: nat_hooks });
        let trigger = engine.add_op("trigger", vec![], state);
        let faulting = engine.add_op("faulting", vec![], state);
        engine
            .bind_host_function(faulting, "counter.fail", no_hooks())
            .expect("bind counter fault reducer");
        let triple = engine.add_op("triple", vec![nat, nat, state], state);
        let pair = engine.add_op("pair", vec![nat, nat], state);
        engine.add_rule(Term::constant(trigger), Term::constant(faulting), 0);

        // Rule-fair: `tick`, then `tock`, then `trigger => faulting`, whose reduction faults.
        // Position-fair: the same three positions in one pass.
        let leaves = [tick, tock, trigger].map(|symbol| engine.make_const(symbol));
        let initial = engine.make_free(triple, leaves.to_vec());
        let mut rewriting = if position_fair {
            engine.frewrite(initial, 1)
        } else {
            engine.rewrite(initial)
        };
        let fault = rewriting
            .try_run(&mut engine, None)
            .expect_err("reducing `faulting` after both counters fired");
        assert_fault(&fault, "counter.fail", "counter fault");
        assert_eq!(calls.load(Ordering::SeqCst), 1);
        assert_eq!(rewriting.current(), initial);
        assert_eq!(engine.rewrites(), 0);

        let counters = [tick, tock].map(|symbol| engine.make_const(symbol));
        let fresh = engine.make_free(pair, counters.to_vec());
        let mut rewriting = if position_fair {
            engine.frewrite(fresh, 1)
        } else {
            engine.rewrite(fresh)
        };
        let step = rewriting
            .try_run(&mut engine, None)
            .expect("counters alone rewrite to a normal form");
        assert!(step.done);
        assert_eq!(engine.node(step.term).symbol(), pair);
        let values: Vec<String> = engine
            .node(step.term)
            .children()
            .map(|value| counter_numeral(&engine, value, zero))
            .collect();
        assert_eq!(
            values,
            ["0", "0"],
            "position_fair = {position_fair}: both counters restart after the rollback"
        );
    }
}

#[test]
fn outer_fault_rolls_back_child_rewrite_and_invalidates_its_cache_stamp() {
    let calls = Arc::new(AtomicUsize::new(0));
    let catalog = HostFunctionCatalog::builder()
        .register(
            "outer.fail",
            CountedFaultReducer {
                calls: Arc::clone(&calls),
                message: "outer fault",
            },
            unary_descriptor(),
        )
        .expect("register outer fault reducer")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let sort = engine.add_sort("S");
    engine.close_sorts();
    let a = engine.add_op("a", vec![], sort);
    let b = engine.add_op("b", vec![], sort);
    let inner = engine.add_op("inner", vec![sort], sort);
    let outer = engine.add_op("outer", vec![sort], sort);
    engine.add_equation(Equation {
        lhs: Term::op(inner, vec![Term::constant(a)]),
        rhs: Term::constant(b),
        nr_vars: 0,
    });
    engine
        .bind_host_function(outer, "outer.fail", no_hooks())
        .expect("bind outer fault reducer");
    engine.set_trace(true);

    let a_dag = engine.make_const(a);
    let child = engine.make_free(inner, vec![a_dag]);
    let redex = engine.make_free(outer, vec![child]);
    let first = engine
        .try_reduce(redex)
        .expect_err("outer reducer faults after child normalization");
    assert_fault(&first, "outer.fail", "outer fault");
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_no_semantic_effects(&mut engine);

    let child_result = engine
        .try_reduce(child)
        .expect("stale child cache is recomputed after the fault");
    assert_eq!(engine.node(child_result).symbol(), b);
    assert_eq!(engine.rewrites(), 1);
    assert_eq!(engine.rewrite_breakdown(), (0, 0, 0, 0));
    assert!(matches!(
        engine.take_trace().as_slice(),
        [TraceEvent::Rewrite {
            kind: RewriteKind::Equation,
            ..
        }]
    ));

    engine.reset_rewrites();
    let second = engine
        .try_reduce(redex)
        .expect_err("retry still dispatches the outer reducer");
    assert_eq!(first, second);
    assert_eq!(calls.load(Ordering::SeqCst), 2);
    assert_no_semantic_effects(&mut engine);
}

#[derive(Clone, Copy)]
enum NestedIdentityExit {
    Decline,
    Fault,
}

#[derive(Clone, Copy)]
struct BuildThenExit {
    exit: NestedIdentityExit,
}

impl StrictReducer for BuildThenExit {
    fn reduce<'ctx>(
        &self,
        ctx: &mut StrictReduceCtx<'ctx>,
        call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        let value = ctx.constant(call.hooks().term_symbol("valueTerm"))?;
        let plus = call.hooks().op_symbol("plusSymbol");
        let _built = ctx.app(plus, &[value.as_ref(), value.as_ref()])?;
        match self.exit {
            NestedIdentityExit::Decline => Ok(StrictOutcome::Decline),
            NestedIdentityExit::Fault => Err(ReducerFault::new("outer callback fault")),
        }
    }
}

#[test]
fn nested_identity_fault_wins_and_is_consumed_for_callback_error_and_decline() {
    let identity_calls = Arc::new(AtomicUsize::new(0));
    let builder_descriptor = || {
        StrictReducerDescriptor::builder(0)
            .require_op_hook(
                "plusSymbol",
                &[HookSort::Result, HookSort::Result],
                HookSort::Result,
            )
            .require_constant_term_hook("valueTerm", HookSort::Result)
            .build()
    };
    let catalog = HostFunctionCatalog::builder()
        .register(
            "nested.identity-fail",
            CountedFaultReducer {
                calls: Arc::clone(&identity_calls),
                message: "nested identity fault",
            },
            StrictReducerDescriptor::builder(0).build(),
        )
        .expect("register identity fault reducer")
        .register(
            "nested.outer-fail",
            BuildThenExit {
                exit: NestedIdentityExit::Fault,
            },
            builder_descriptor(),
        )
        .expect("register outer fault reducer")
        .register(
            "nested.outer-decline",
            BuildThenExit {
                exit: NestedIdentityExit::Decline,
            },
            builder_descriptor(),
        )
        .expect("register outer declining reducer")
        .build();
    let mut engine = Engine::with_host_functions(catalog);
    let sort = engine.add_sort("S");
    engine.close_sorts();
    let bad_identity = engine.add_op("badIdentity", vec![], sort);
    let value = engine.add_op("value", vec![], sort);
    let unrelated = engine.add_op("unrelated", vec![], sort);
    let plus = engine.add_op_ac("plus", vec![sort, sort], sort, Some(bad_identity));
    let outer_fault = engine.add_op("outerFault", vec![], sort);
    let outer_decline = engine.add_op("outerDecline", vec![], sort);
    engine
        .bind_host_function(bad_identity, "nested.identity-fail", no_hooks())
        .expect("bind identity fault reducer");
    for (outer, key) in [
        (outer_fault, "nested.outer-fail"),
        (outer_decline, "nested.outer-decline"),
    ] {
        engine
            .bind_host_function(
                outer,
                key,
                ResolvedHostHooks::builder()
                    .op("plusSymbol", plus)
                    .constant_term("valueTerm", value)
                    .build()
                    .expect("builder hooks"),
            )
            .expect("bind outer reducer");
    }
    engine.set_trace(true);

    for outer in [outer_fault, outer_decline] {
        let redex = engine.make_const(outer);
        let fault = engine
            .try_reduce(redex)
            .expect_err("nested identity fault must win");
        assert_fault(&fault, "nested.identity-fail", "nested identity fault");
        assert_no_semantic_effects(&mut engine);

        let ordinary = engine.make_const(unrelated);
        assert_eq!(
            engine
                .try_reduce(ordinary)
                .expect("no deferred fault leaks into an unrelated reduction"),
            ordinary
        );
        assert_no_semantic_effects(&mut engine);
    }
    assert_eq!(identity_calls.load(Ordering::SeqCst), 2);
}
