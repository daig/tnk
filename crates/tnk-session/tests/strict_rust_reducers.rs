use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use tnk_core::host::{
    HookSort, HostFunctionCatalog, HostFunctionRegistrationError, ReducerFault, StrictCall,
    StrictOutcome, StrictReduceCtx, StrictReducer, StrictReducerDescriptor, codecs,
};
use tnk_frontend::load::load_source_with_host_functions;
use tnk_modules::load::load_program_with_host_functions;
use tnk_session::Session;

fn normalize_tag(input: &[u8]) -> Vec<u8> {
    let mut output = Vec::with_capacity(input.len());
    let mut separator_pending = false;
    for &byte in input {
        if byte.is_ascii_alphanumeric() {
            if separator_pending && !output.is_empty() {
                output.push(b'-');
            }
            output.push(byte.to_ascii_lowercase());
            separator_pending = false;
        } else {
            separator_pending = !output.is_empty();
        }
    }
    output
}

fn trim_edge_slashes(mut value: &[u8]) -> &[u8] {
    while value.first() == Some(&b'/') {
        value = &value[1..];
    }
    while value.last() == Some(&b'/') {
        value = &value[..value.len() - 1];
    }
    value
}

fn join_path(left: &[u8], right: &[u8]) -> Vec<u8> {
    let left = trim_edge_slashes(left);
    let right = trim_edge_slashes(right);
    let needs_separator = !left.is_empty() && !right.is_empty();
    let mut output = Vec::with_capacity(left.len() + right.len() + usize::from(needs_separator));
    output.extend_from_slice(left);
    if needs_separator {
        output.push(b'/');
    }
    output.extend_from_slice(right);
    output
}

#[derive(Clone, Debug, Default)]
struct PreferConfigured {
    calls: Option<Arc<AtomicUsize>>,
}

impl StrictReducer for PreferConfigured {
    fn reduce<'ctx>(
        &self,
        ctx: &mut StrictReduceCtx<'ctx>,
        call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        if let Some(calls) = &self.calls {
            calls.fetch_add(1, Ordering::SeqCst);
        }
        let first = call.argument(0);
        let second = call.argument(1);
        let chosen = if !ctx.is_ground(first) {
            second
        } else {
            let preferred = call.hooks().term_symbol("preferredTerm");
            if !preferred.matches(ctx.top(first.as_ref())) {
                return Ok(StrictOutcome::Decline);
            }
            first
        };
        let selected = call.hooks().op_symbol("selectedSymbol");
        Ok(StrictOutcome::Reduced(
            ctx.app(selected, &[chosen.as_ref()])?,
        ))
    }
}

#[derive(Clone, Copy, Debug, Default)]
struct FaultReducer;

impl StrictReducer for FaultReducer {
    fn reduce<'ctx>(
        &self,
        _ctx: &mut StrictReduceCtx<'ctx>,
        _call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        Err(ReducerFault::new("deliberate fixture fault"))
    }
}

fn catalog() -> HostFunctionCatalog {
    catalog_with_call_counters(None, None, None)
}

fn catalog_with_call_counters(
    normalize_calls: Option<Arc<AtomicUsize>>,
    join_calls: Option<Arc<AtomicUsize>>,
    prefer_calls: Option<Arc<AtomicUsize>>,
) -> HostFunctionCatalog {
    let prefer_descriptor = StrictReducerDescriptor::builder(2)
        .require_op_hook("selectedSymbol", &[HookSort::Argument(0)], HookSort::Result)
        .require_constant_term_hook("preferredTerm", HookSort::Argument(0))
        .build();
    HostFunctionCatalog::builder()
        .register_typed1(
            "text.normalize-tag",
            codecs::string(),
            codecs::string(),
            move |input: &[u8]| {
                if let Some(calls) = &normalize_calls {
                    calls.fetch_add(1, Ordering::SeqCst);
                }
                normalize_tag(input)
            },
        )
        .expect("register unary reducer")
        .register_typed2(
            "path.join",
            codecs::string(),
            codecs::string(),
            codecs::string(),
            move |left: &[u8], right: &[u8]| {
                if let Some(calls) = &join_calls {
                    calls.fetch_add(1, Ordering::SeqCst);
                }
                join_path(left, right)
            },
        )
        .expect("register binary reducer")
        .register(
            "routing.prefer-configured",
            PreferConfigured {
                calls: prefer_calls,
            },
            prefer_descriptor,
        )
        .expect("register symbolic reducer")
        .register(
            "testing.fail",
            FaultReducer,
            StrictReducerDescriptor::builder(1).build(),
        )
        .expect("register fault reducer")
        .register(
            "testing.fail-zero",
            FaultReducer,
            StrictReducerDescriptor::builder(0).build(),
        )
        .expect("register zero-arity fault reducer")
        .build()
}

fn configured_session() -> Session {
    Session::builder()
        .host_functions(catalog())
        .reduce_gc_interval(Some(1))
        .build()
}

fn assert_in_order(output: &str, parts: &[&str]) {
    let mut cursor = 0;
    for part in parts {
        let offset = output[cursor..]
            .find(part)
            .unwrap_or_else(|| panic!("missing ordered trace fragment `{part}` in:\n{output}"));
        cursor += offset + part.len();
    }
}

fn assert_rewrite_counts(output: &str, expected: &[u64]) {
    let actual: Vec<u64> = output
        .lines()
        .filter_map(|line| line.strip_prefix("rewrites: ")?.parse().ok())
        .collect();
    assert_eq!(actual, expected, "{output}");
}

const HOST_SCALARS_FIXTURE: &str = r#"fmod HOST-SCALARS is
  sort String .
  op <Strings> : -> String [ctor special (id-hook StringSymbol)] .
  op opaque : -> String [ctor] .
  op ordinary : -> String [ctor] .
  op rawTag : -> String .
  op leftPart : -> String .
  op rightPart : -> String .
  eq rawTag = "  TNK / Reducers  " .
  eq leftPart = "api/" .
  eq rightPart = "/v1" .
  op normalizeTag : String -> String
    [special (id-hook HostFunctionSymbol (text.normalize-tag)
              op-hook stringSymbol (<Strings> : ~> String))] .
  op joinPath : String String -> String
    [special (id-hook HostFunctionSymbol (path.join)
              op-hook stringSymbol (<Strings> : ~> String))] .
  eq normalizeTag(ordinary) = "ordinary-equation" .
  eq normalizeTag(opaque) = "opaque-fallback" [owise] .
endfm
fmod HOST-SCALARS-RENAMED is
  protecting HOST-SCALARS * (
    op <Strings> to <HostStrings>,
    op normalizeTag to slug,
    op joinPath to _join_
  ) .
endfm"#;

const ROUTING_FIXTURE: &str = r#"fth ROUTABLE is
  sort Elt .
  op preferred : -> Elt [pconst] .
endfth
fmod ROUTING{X :: ROUTABLE} is
  sort Decision{X} .
  op none : -> Decision{X} [ctor] .
  op hostLost : -> Decision{X} [ctor] .
  op selected : X$Elt -> Decision{X} [ctor] .
  op prefer : X$Elt X$Elt -> Decision{X}
    [special (id-hook HostFunctionSymbol (routing.prefer-configured)
              op-hook selectedSymbol (selected : X$Elt ~> Decision{X})
              term-hook preferredTerm (X$preferred))] .
  vars A B : X$Elt .
  eq prefer(X$preferred, B) = hostLost .
  eq selected(X$preferred) = none .
  eq prefer(A, B) = none [owise] .
endfm
fmod COLORS is
  sort Color .
  ops red blue green : -> Color [ctor] .
endfm
view ColorView from ROUTABLE to COLORS is
  sort Elt to Color .
  op preferred to red .
endv
fmod COLOR-ROUTING is
  protecting ROUTING{ColorView} .
endfm
fmod COLOR-ROUTING-RENAMED is
  protecting COLOR-ROUTING * (
    op prefer to choose,
    op selected to picked
  ) .
endfm"#;

#[test]
fn typed_reducers_normalize_arguments_decline_and_survive_renaming() {
    let normalize_calls = Arc::new(AtomicUsize::new(0));
    let join_calls = Arc::new(AtomicUsize::new(0));
    let mut session = Session::builder()
        .host_functions(catalog_with_call_counters(
            Some(Arc::clone(&normalize_calls)),
            Some(Arc::clone(&join_calls)),
            None,
        ))
        .reduce_gc_interval(Some(1))
        .build();
    let entered = session.eval(HOST_SCALARS_FIXTURE, false);
    assert_eq!(entered.output, "");

    let unary = session.eval(
        "set trace on .\nreduce in HOST-SCALARS-RENAMED : slug(rawTag) .",
        false,
    );
    assert!(
        unary.output.contains("result String: \"tnk-reducers\""),
        "{}",
        unary.output
    );
    assert_rewrite_counts(&unary.output, &[2]);
    assert!(
        unary.output.contains("text.normalize-tag"),
        "{}",
        unary.output
    );
    assert!(unary.output.contains("symbol slug"), "{}", unary.output);
    assert_in_order(
        &unary.output,
        &[
            "eq rawTag =",
            "(strict Rust reducer text.normalize-tag for symbol slug)",
        ],
    );
    assert_eq!(unary.output.matches("(strict Rust reducer ").count(), 1);
    let host_trace_start = unary
        .output
        .find("(strict Rust reducer text.normalize-tag")
        .expect("typed unary host trace");
    let host_trace_end = unary.output[host_trace_start..]
        .find("rewrites:")
        .map(|offset| host_trace_start + offset)
        .expect("rewrite summary after typed unary host trace");
    let host_trace = &unary.output[host_trace_start..host_trace_end];
    for expected in ["slug", "--->", "\"tnk-reducers\""] {
        assert!(host_trace.contains(expected), "{host_trace}");
    }
    assert_eq!(normalize_calls.load(Ordering::SeqCst), 1);

    let binary = session.eval(
        "reduce in HOST-SCALARS-RENAMED : leftPart join rightPart .",
        false,
    );
    assert!(
        binary.output.contains("result String: \"api/v1\""),
        "{}",
        binary.output
    );
    assert_rewrite_counts(&binary.output, &[3]);
    assert!(binary.output.contains("path.join"), "{}", binary.output);
    assert_in_order(
        &binary.output,
        &[
            "eq leftPart =",
            "eq rightPart =",
            "(strict Rust reducer path.join for symbol _join_)",
        ],
    );
    assert_eq!(binary.output.matches("(strict Rust reducer ").count(), 1);
    assert_eq!(join_calls.load(Ordering::SeqCst), 1);

    let binary_decline = session.eval(
        "reduce in HOST-SCALARS-RENAMED : leftPart join opaque .",
        false,
    );
    assert!(
        binary_decline.output.contains("result String:"),
        "{}",
        binary_decline.output
    );
    assert_rewrite_counts(&binary_decline.output, &[1]);
    assert!(
        !binary_decline.output.contains("path.join"),
        "{}",
        binary_decline.output
    );
    assert_eq!(join_calls.load(Ordering::SeqCst), 1);

    let decline = session.eval("reduce in HOST-SCALARS-RENAMED : slug(opaque) .", false);
    assert!(
        decline
            .output
            .contains("result String: \"opaque-fallback\""),
        "{}",
        decline.output
    );
    assert_rewrite_counts(&decline.output, &[1]);
    assert!(
        !decline.output.contains("text.normalize-tag"),
        "{}",
        decline.output
    );
    assert_eq!(normalize_calls.load(Ordering::SeqCst), 1);
}

#[test]
fn symbolic_reducer_survives_parameters_views_instantiation_and_renaming() {
    let prefer_calls = Arc::new(AtomicUsize::new(0));
    let mut session = Session::builder()
        .host_functions(catalog_with_call_counters(
            None,
            None,
            Some(Arc::clone(&prefer_calls)),
        ))
        .reduce_gc_interval(Some(1))
        .build();
    let entered = session.eval(ROUTING_FIXTURE, false);
    assert_eq!(entered.output, "");

    let preferred = session.eval(
        "set trace on .\nreduce in COLOR-ROUTING-RENAMED : choose(red, green) .",
        false,
    );
    assert!(
        preferred
            .output
            .contains("result Decision{ColorView}: none"),
        "{}",
        preferred.output
    );
    assert_rewrite_counts(&preferred.output, &[2]);
    assert!(
        preferred.output.contains("routing.prefer-configured"),
        "{}",
        preferred.output
    );
    assert!(
        preferred.output.contains("symbol choose"),
        "{}",
        preferred.output
    );
    assert!(
        !preferred.output.contains("hostLost"),
        "{}",
        preferred.output
    );
    assert_in_order(
        &preferred.output,
        &[
            "(strict Rust reducer routing.prefer-configured for symbol choose)",
            "eq picked(",
        ],
    );
    assert_eq!(
        preferred
            .output
            .matches("(strict Rust reducer routing.prefer-configured")
            .count(),
        1
    );
    assert_eq!(prefer_calls.load(Ordering::SeqCst), 1);

    let symbolic = session.eval(
        "reduce in COLOR-ROUTING-RENAMED : choose(X:Color, blue) .",
        false,
    );
    assert!(
        symbolic
            .output
            .contains("result Decision{ColorView}: picked(blue)"),
        "{}",
        symbolic.output
    );
    assert_rewrite_counts(&symbolic.output, &[1]);
    assert!(!symbolic.output.contains("hostLost"), "{}", symbolic.output);
    assert_eq!(prefer_calls.load(Ordering::SeqCst), 2);

    let decline = session.eval(
        "reduce in COLOR-ROUTING-RENAMED : choose(green, blue) .",
        false,
    );
    assert!(
        decline.output.contains("result Decision{ColorView}: none"),
        "{}",
        decline.output
    );
    assert_rewrite_counts(&decline.output, &[1]);
    assert!(
        !decline.output.contains("routing.prefer-configured"),
        "{}",
        decline.output
    );
    assert_eq!(
        prefer_calls.load(Ordering::SeqCst),
        3,
        "Decline must follow exactly one strict callback invocation"
    );
    let pre_rebuild = session.eval("rewrite [1] red .", false);
    assert!(
        pre_rebuild.output.contains("result Color: red"),
        "{}",
        pre_rebuild.output
    );

    let redefined = session.eval(
        r#"fmod COLORS is
  sort Color .
  ops red blue green yellow : -> Color [ctor] .
endfm"#,
        false,
    );
    assert_eq!(redefined.output, "");
    let cleared = session.eval("continue .", false);
    assert!(
        cleared.output.contains("error: no previous rewriting"),
        "{}",
        cleared.output
    );
    let rebuilt = session.eval(
        "reduce in COLOR-ROUTING-RENAMED : choose(red, green) .",
        false,
    );
    assert!(
        rebuilt.output.contains("result Decision{ColorView}: none"),
        "{}",
        rebuilt.output
    );
    assert_rewrite_counts(&rebuilt.output, &[2]);
    assert!(
        rebuilt.output.contains("routing.prefer-configured"),
        "{}",
        rebuilt.output
    );
    let rebuilt_new_symbol = session.eval(
        "reduce in COLOR-ROUTING-RENAMED : choose(yellow, blue) .",
        false,
    );
    assert!(
        rebuilt_new_symbol
            .output
            .contains("result Decision{ColorView}: none"),
        "{}",
        rebuilt_new_symbol.output
    );
    assert_rewrite_counts(&rebuilt_new_symbol.output, &[1]);
    assert!(
        !rebuilt_new_symbol
            .output
            .contains("routing.prefer-configured"),
        "{}",
        rebuilt_new_symbol.output
    );
    let rebuilt_symbolic = session.eval(
        "reduce in COLOR-ROUTING-RENAMED : choose(X:Color, blue) .",
        false,
    );
    assert!(
        rebuilt_symbolic
            .output
            .contains("result Decision{ColorView}: picked(blue)"),
        "{}",
        rebuilt_symbolic.output
    );
    assert_rewrite_counts(&rebuilt_symbolic.output, &[1]);
    assert!(
        rebuilt_symbolic
            .output
            .contains("routing.prefer-configured"),
        "{}",
        rebuilt_symbolic.output
    );
    let rebuilt_decline = session.eval(
        "reduce in COLOR-ROUTING-RENAMED : choose(green, blue) .",
        false,
    );
    assert!(
        rebuilt_decline
            .output
            .contains("result Decision{ColorView}: none"),
        "{}",
        rebuilt_decline.output
    );
    assert_rewrite_counts(&rebuilt_decline.output, &[1]);
    assert!(
        !rebuilt_decline.output.contains("routing.prefer-configured"),
        "{}",
        rebuilt_decline.output
    );
    assert_eq!(
        session.eval("select COLOR-ROUTING-RENAMED .", false).output,
        ""
    );
    let partial = session.eval("rewrite [1] choose(red, green) .", false);
    assert!(
        partial.output.contains("result Decision{ColorView}: none"),
        "{}",
        partial.output
    );
    let invalidated = session.eval(
        r#"fmod COLORS is
  sort Color .
  ops blue green yellow : -> Color [ctor] .
endfm"#,
        false,
    );
    assert!(
        invalidated.output.contains("ColorView") || invalidated.output.contains("COLOR-ROUTING"),
        "{}",
        invalidated.output
    );
    let stale = session.eval(
        "reduce in COLOR-ROUTING-RENAMED : choose(blue, green) .",
        false,
    );
    assert!(
        stale.output.contains("does not exist"),
        "failed dependent rebuild retained a stale Engine: {}",
        stale.output
    );
    let stale_intermediate = session.eval("reduce in COLOR-ROUTING : prefer(blue, green) .", false);
    assert!(
        stale_intermediate.output.contains("does not exist"),
        "failed dependent rebuild retained an intermediate stale Engine: {}",
        stale_intermediate.output
    );
    let continuation = session.eval("continue .", false);
    assert!(
        continuation.output.contains("error: no previous rewriting"),
        "{}",
        continuation.output
    );
}

#[test]
fn reducer_faults_abort_every_semantic_driver_without_continuations() {
    let mut session = configured_session();
    let entered = session.eval(
        r#"mod HOST-FAULT is
  sort Elt .
  ops a b none : -> Elt [ctor] .
  op fail : Elt -> Elt
    [special (id-hook HostFunctionSymbol (testing.fail))] .
  op _+_ : Elt Elt -> Elt [assoc comm id: none] .
  rl a => fail(a) .
endm
smod HOST-FAULT-STRAT is
  protecting HOST-FAULT .
  strat go @ Elt .
  sd go := idle .
endsm
mod HOST-FAULT-COND is
  protecting HOST-FAULT .
  var X : Elt .
  op test : Elt -> Elt .
  crl test(X) => b if fail(X) = b .
endm
mod HOST-FAULT-KEEP is
  sort K .
  ops k0 k1 k2 : -> K [ctor] .
  rl k0 => k1 .
  rl k1 => k2 .
endm
mod HOST-FAULT-RESUME is
  protecting HOST-FAULT .
  ops k0 k1 : -> Elt [ctor] .
  rl k0 => k1 .
  rl k1 => fail(k1) .
endm"#,
        false,
    );
    assert_eq!(entered.output, "");

    for (command, key) in [
        ("reduce in HOST-FAULT : fail(a) .", "testing.fail"),
        ("rewrite in HOST-FAULT : a .", "testing.fail"),
        ("frewrite in HOST-FAULT : a .", "testing.fail"),
        ("erewrite in HOST-FAULT : a .", "testing.fail"),
        ("search in HOST-FAULT : a =>+ X:Elt .", "testing.fail"),
        ("match in HOST-FAULT : X:Elt <=? fail(a) .", "testing.fail"),
        ("xmatch in HOST-FAULT : X:Elt <=? fail(a) .", "testing.fail"),
        ("get variants [1] in HOST-FAULT : fail(a) .", "testing.fail"),
        (
            "get irredundant variants [1] in HOST-FAULT : fail(a) .",
            "testing.fail",
        ),
        (
            "variant unify [1] in HOST-FAULT : X:Elt =? fail(a) .",
            "testing.fail",
        ),
        (
            "filtered variant unify [1] in HOST-FAULT : X:Elt =? fail(a) .",
            "testing.fail",
        ),
        (
            "variant match [1] in HOST-FAULT : fail(X:Elt) <=? a .",
            "testing.fail",
        ),
        (
            "vu-narrow [1] in HOST-FAULT : fail(a) =>* X:Elt .",
            "testing.fail",
        ),
        (
            "fvu-narrow [1] in HOST-FAULT : fail(a) =>* X:Elt .",
            "testing.fail",
        ),
        (
            "srewrite in HOST-FAULT-STRAT : fail(a) using go .",
            "testing.fail",
        ),
        (
            "dsrewrite in HOST-FAULT-STRAT : fail(a) using go .",
            "testing.fail",
        ),
        ("rewrite in HOST-FAULT-COND : test(a) .", "testing.fail"),
    ] {
        let seeded = session.eval("rewrite [1] in HOST-FAULT-KEEP : k0 .", false);
        assert!(seeded.output.contains("result K: k1"), "{}", seeded.output);
        assert!(
            !session
                .eval("show path .", false)
                .output
                .contains("error: no previous rewriting"),
            "{command}: bounded rewrite did not seed a continuation"
        );
        let expected = format!("error: strict reducer `{key}` failed: deliberate fixture fault");
        let result = session.eval(command, false);
        assert_eq!(result.output, expected, "{command}");
        let continuation = session.eval("continue .", false);
        assert!(
            continuation.output.contains("error: no previous rewriting"),
            "{command}: {}",
            continuation.output
        );
    }

    let rewrite_seed = session.eval("rewrite [1] in HOST-FAULT-RESUME : k0 .", false);
    assert!(
        rewrite_seed.output.contains("result Elt: k1"),
        "{}",
        rewrite_seed.output
    );
    let resumed_fault = session.eval("continue 1 .", false);
    assert_eq!(
        resumed_fault.output,
        "error: strict reducer `testing.fail` failed: deliberate fixture fault"
    );
    assert!(
        session
            .eval("continue .", false)
            .output
            .contains("error: no previous rewriting")
    );

    let search_seed = session.eval("search [1] in HOST-FAULT-RESUME : k0 =>+ X:Elt .", false);
    assert!(
        search_seed.output.contains("Solution 1"),
        "{}",
        search_seed.output
    );
    let resumed_search_fault = session.eval("continue 1 .", false);
    assert_eq!(
        resumed_search_fault.output,
        "error: strict reducer `testing.fail` failed: deliberate fixture fault"
    );
    assert!(
        session
            .eval("continue .", false)
            .output
            .contains("error: no previous rewriting")
    );
}

const HOST_BOTH_SOURCE: &str = r#"fmod HOST-SCALARS is
  sort String .
  op <Strings> : -> String [ctor special (id-hook StringSymbol)] .
  op normalizeTag : String -> String
    [special (id-hook HostFunctionSymbol (text.normalize-tag)
              op-hook stringSymbol (<Strings> : ~> String))] .
  op joinPath : String String -> String
    [special (id-hook HostFunctionSymbol (path.join)
              op-hook stringSymbol (<Strings> : ~> String))] .
endfm"#;

#[derive(Clone)]
struct CountDecline {
    calls: Arc<AtomicUsize>,
}

impl StrictReducer for CountDecline {
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
struct ZeroReducer {
    calls: Arc<AtomicUsize>,
}

impl StrictReducer for ZeroReducer {
    fn reduce<'ctx>(
        &self,
        ctx: &mut StrictReduceCtx<'ctx>,
        call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        self.calls.fetch_add(1, Ordering::SeqCst);
        if !call.arguments().is_empty() {
            return Err(ReducerFault::new("zero-arity reducer received arguments"));
        }
        let result = call.hooks().term_symbol("resultTerm");
        Ok(StrictOutcome::Reduced(ctx.constant(result)?))
    }
}

#[derive(Clone, Copy)]
struct EchoSelectedRange;

impl StrictReducer for EchoSelectedRange {
    fn reduce<'ctx>(
        &self,
        ctx: &mut StrictReduceCtx<'ctx>,
        call: StrictCall<'ctx>,
    ) -> Result<StrictOutcome<'ctx>, ReducerFault> {
        if call.argument_sorts()[0] != call.result_range() {
            return Err(ReducerFault::new(
                "selected declaration range did not match the actual argument",
            ));
        }
        Ok(StrictOutcome::Reduced(ctx.reuse(call.argument(0))))
    }
}

#[test]
fn catalog_registration_errors_are_typed_and_atomic() {
    fn assert_send_sync_static<T: Send + Sync + 'static>() {}
    fn assert_reducer<T: StrictReducer>() {}
    assert_send_sync_static::<HostFunctionCatalog>();
    assert_reducer::<PreferConfigured>();
    assert_reducer::<FaultReducer>();

    let duplicate = HostFunctionCatalog::builder()
        .register(
            "valid.reducer",
            FaultReducer,
            StrictReducerDescriptor::builder(1).build(),
        )
        .expect("first registration")
        .register(
            "valid.reducer",
            FaultReducer,
            StrictReducerDescriptor::builder(1).build(),
        )
        .err()
        .expect("duplicate registration must fail");
    assert!(matches!(
        duplicate,
        HostFunctionRegistrationError::DuplicateKey(key) if key.as_str() == "valid.reducer"
    ));

    for invalid in [
        "",
        "1a.b",
        "single",
        "Upper.case",
        "under_score.key",
        "slash/key.name",
        "white space.key",
        "a..b",
        ".a.b",
        "a.b.",
        "-a.b",
        "a.-b",
        "a.1b",
        "a-.b",
        "a.b-",
        "a.b!",
    ] {
        let error = HostFunctionCatalog::builder()
            .register(
                invalid,
                FaultReducer,
                StrictReducerDescriptor::builder(1).build(),
            )
            .err()
            .unwrap_or_else(|| panic!("invalid key `{invalid}` was accepted"));
        assert!(
            matches!(&error, HostFunctionRegistrationError::InvalidKey(key) if key == invalid),
            "{invalid}: {error}"
        );
    }

    let duplicate_purpose = StrictReducerDescriptor::builder(1)
        .require_op_hook("same", &[], HookSort::Result)
        .require_constant_term_hook("same", HookSort::Result)
        .build();
    assert!(matches!(
        HostFunctionCatalog::builder()
            .register("invalid.descriptor", FaultReducer, duplicate_purpose)
            .err()
            .expect("duplicate purpose must fail"),
        HostFunctionRegistrationError::InvalidDescriptor(message)
            if message.contains("duplicate hook purpose")
    ));

    let bad_argument = StrictReducerDescriptor::builder(1)
        .require_op_hook("outside", &[HookSort::Argument(1)], HookSort::Result)
        .build();
    assert!(matches!(
        HostFunctionCatalog::builder()
            .register("invalid.argument", FaultReducer, bad_argument)
            .err()
            .expect("out-of-range descriptor argument must fail"),
        HostFunctionRegistrationError::InvalidDescriptor(message)
            if message.contains("outside arity 1")
    ));
}

fn assert_failed_load_preserves_session(mut session: Session) {
    let setup = session.eval(
        r#"mod KEEP is
  sort S .
  ops a b c : -> S [ctor] .
  rl a => b .
  rl b => c .
endm
rewrite [1] in KEEP : a ."#,
        false,
    );
    assert!(setup.output.contains("result S: b"), "{}", setup.output);

    let failed = session.eval(HOST_BOTH_SOURCE, false);
    assert!(
        failed.output.contains("module `HOST-SCALARS`"),
        "{}",
        failed.output
    );
    assert!(
        failed
            .output
            .contains("missing host capability `text.normalize-tag`"),
        "{}",
        failed.output
    );
    let continued = session.eval("continue 1 .", false);
    assert!(
        continued.output.contains("result S: c"),
        "{}",
        continued.output
    );
    let leaked_import = session.eval(
        "fmod HOST-LEAK-CHECK is protecting HOST-SCALARS . endfm",
        false,
    );
    assert!(
        leaked_import.output.contains("HOST-SCALARS"),
        "{}",
        leaked_import.output
    );
    assert!(
        !leaked_import.output.contains("missing host capability"),
        "failed module leaked into the source database: {}",
        leaked_import.output
    );
}

#[test]
fn empty_and_partial_catalog_loads_are_atomic() {
    assert_failed_load_preserves_session(Session::new());
    assert_failed_load_preserves_session(Session::builder().build());

    let unary_only = HostFunctionCatalog::builder()
        .register_typed1(
            "text.normalize-tag",
            codecs::string(),
            codecs::string(),
            normalize_tag,
        )
        .expect("register unary fixture")
        .build();
    let mut partial = Session::builder().host_functions(unary_only).build();
    let prior = partial.eval("fmod PRIOR is sort P . op p : -> P [ctor] . endfm", false);
    assert_eq!(prior.output, "");
    let failed = partial.eval(HOST_BOTH_SOURCE, false);
    assert!(failed.output.contains("joinPath"), "{}", failed.output);
    assert!(
        failed
            .output
            .contains("missing host capability `path.join`"),
        "{}",
        failed.output
    );
    let still_prior = partial.eval("reduce in PRIOR : p .", false);
    assert!(
        still_prior.output.contains("result P: p"),
        "{}",
        still_prior.output
    );

    let mut full = configured_session();
    assert_eq!(full.eval(HOST_BOTH_SOURCE, false).output, "");
}

#[test]
fn configured_frontend_and_module_loaders_share_the_core_catalog() {
    let functions = catalog();
    assert!(
        load_source_with_host_functions(HOST_BOTH_SOURCE, &functions).is_ok(),
        "configured import-free frontend loader"
    );
    assert!(
        load_program_with_host_functions(HOST_BOTH_SOURCE, &functions).is_ok(),
        "configured flattened module loader"
    );
    let empty = HostFunctionCatalog::default();
    let frontend_error = load_source_with_host_functions(HOST_BOTH_SOURCE, &empty)
        .err()
        .expect("empty frontend catalog must reject host attachment");
    assert!(
        frontend_error.contains("text.normalize-tag"),
        "{frontend_error}"
    );
    let module_error = load_program_with_host_functions(HOST_BOTH_SOURCE, &empty)
        .err()
        .expect("empty module catalog must reject host attachment");
    assert!(
        module_error.contains("text.normalize-tag"),
        "{module_error}"
    );
}

#[test]
fn host_binding_survives_plain_and_diamond_imports_once() {
    let functions = HostFunctionCatalog::builder()
        .register(
            "imports.echo",
            EchoSelectedRange,
            StrictReducerDescriptor::builder(1).build(),
        )
        .expect("register import fixture")
        .build();
    let mut session = Session::builder().host_functions(functions).build();
    let output = session
        .eval(
            r#"fmod HOST-IMPORT-BASE is
  sort S .
  op a : -> S [ctor] .
  op echo : S -> S
    [special (id-hook HostFunctionSymbol (imports.echo))] .
endfm
fmod HOST-IMPORT-PLAIN is
  protecting HOST-IMPORT-BASE .
endfm
fmod HOST-IMPORT-LEFT is
  protecting HOST-IMPORT-BASE .
endfm
fmod HOST-IMPORT-RIGHT is
  protecting HOST-IMPORT-BASE .
endfm
fmod HOST-IMPORT-DIAMOND is
  protecting HOST-IMPORT-LEFT .
  protecting HOST-IMPORT-RIGHT .
endfm
set trace on .
reduce in HOST-IMPORT-PLAIN : echo(a) .
reduce in HOST-IMPORT-DIAMOND : echo(a) ."#,
            false,
        )
        .output;
    assert_eq!(output.matches("result S: a").count(), 2, "{output}");
    assert_rewrite_counts(&output, &[1, 1]);
    assert_eq!(
        output
            .matches("(strict Rust reducer imports.echo for symbol echo)")
            .count(),
        2,
        "{output}"
    );
}

#[test]
fn host_control_symbol_never_dispatches_through_strict_catalog() {
    let calls = Arc::new(AtomicUsize::new(0));
    let functions = HostFunctionCatalog::builder()
        .register(
            "control.same-key",
            CountDecline {
                calls: Arc::clone(&calls),
            },
            StrictReducerDescriptor::builder(1).build(),
        )
        .expect("register strict key")
        .build();
    let mut session = Session::builder().host_functions(functions).build();
    let output = session
        .eval(
            r#"fmod CONTROL-ONLY is
  sort S .
  op a : -> S [ctor] .
  op control : S -> S
    [special (id-hook HostControlSymbol (control.same-key))] .
endfm
reduce in CONTROL-ONLY : control(a) ."#,
            false,
        )
        .output;
    assert!(output.contains("result S: control(a)"), "{output}");
    assert!(output.contains("rewrites: 0"), "{output}");
    assert_eq!(calls.load(Ordering::SeqCst), 0);
}

fn admission_catalog() -> HostFunctionCatalog {
    let hooked = StrictReducerDescriptor::builder(1)
        .require_op_hook("selectedSymbol", &[HookSort::Argument(0)], HookSort::Result)
        .require_constant_term_hook("preferredTerm", HookSort::Argument(0))
        .build();
    HostFunctionCatalog::builder()
        .register(
            "admission.unary",
            FaultReducer,
            StrictReducerDescriptor::builder(1).build(),
        )
        .expect("register unary admission reducer")
        .register(
            "admission.binary",
            FaultReducer,
            StrictReducerDescriptor::builder(2).build(),
        )
        .expect("register binary admission reducer")
        .register("admission.hooked", FaultReducer, hooked)
        .expect("register hooked admission reducer")
        .build()
}

fn admission_result(extra: &str, declaration: &str) -> String {
    let source = format!(
        r#"fmod ADMISSION is
  sorts S T .
  op a : -> S [ctor] .
  op b : -> T [ctor] .
  op wrap : S -> S [ctor] .
  {extra}
  {declaration}
endfm"#
    );
    Session::builder()
        .host_functions(admission_catalog())
        .build()
        .eval(&source, false)
        .output
}

#[test]
fn attachment_admission_accepts_only_strict_free_standard_schedules() {
    for strategy in ["", "strat (1 2)", "strat (1 2 0)"] {
        let attrs = if strategy.is_empty() {
            "special (id-hook HostFunctionSymbol (admission.binary))".to_string()
        } else {
            format!("{strategy} special (id-hook HostFunctionSymbol (admission.binary))")
        };
        let declaration = format!("op h : S S -> S [{attrs}] .");
        let output = admission_result("", &declaration);
        assert_eq!(output, "", "accepted strategy `{strategy}`: {output}");
    }

    for strategy in ["2 1 0", "0 1 2", "1 0 2 0", "1 1 2 0", "1 0", "0"] {
        let declaration = format!(
            "op h : S S -> S [strat ({strategy}) special (id-hook HostFunctionSymbol (admission.binary))] ."
        );
        let output = admission_result("", &declaration);
        assert!(
            output.contains("strict host operator `h`"),
            "{strategy}: {output}"
        );
        assert!(
            output.contains("argument order 1 through 2"),
            "{strategy}: {output}"
        );
    }

    for declaration in [
        "op h : S S -> S [assoc special (id-hook HostFunctionSymbol (admission.binary))] .",
        "op h : S S -> S [assoc comm special (id-hook HostFunctionSymbol (admission.binary))] .",
        "op h : S S -> S [assoc strat (1 2 0) special (id-hook HostFunctionSymbol (admission.binary))] .",
        "op h : S S -> S [comm special (id-hook HostFunctionSymbol (admission.binary))] .",
        "op h : S -> S [iter special (id-hook HostFunctionSymbol (admission.unary))] .",
    ] {
        let output = admission_result("", declaration);
        assert!(output.contains("strict host operator `h`"), "{output}");
        assert!(output.contains("free root theory"), "{output}");
    }

    let polymorphic = admission_result(
        "",
        "op h : S -> S [poly (1) special (id-hook HostFunctionSymbol (admission.unary))] .",
    );
    assert!(
        polymorphic.contains("cannot use a polymorphic declaration"),
        "{polymorphic}"
    );
}

#[test]
fn attachment_key_arity_and_hook_diagnostics_are_specific() {
    let no_key = admission_result("", "op h : S -> S [special (id-hook HostFunctionSymbol)] .");
    assert!(
        no_key.contains("exactly one HostFunctionSymbol capability key"),
        "{no_key}"
    );
    let two_keys = admission_result(
        "",
        "op h : S -> S [special (id-hook HostFunctionSymbol (admission.unary extra))] .",
    );
    assert!(
        two_keys.contains("exactly one HostFunctionSymbol capability key"),
        "{two_keys}"
    );
    for invalid in ["Upper.case", "a.b-"] {
        let declaration =
            format!("op h : S -> S [special (id-hook HostFunctionSymbol ({invalid}))] .");
        let output = admission_result("", &declaration);
        assert!(
            output.contains(&format!("invalid host-function key `{invalid}`")),
            "{invalid}: {output}"
        );
    }

    let arity = admission_result(
        "",
        "op h : S S -> S [special (id-hook HostFunctionSymbol (admission.unary))] .",
    );
    assert!(arity.contains("requires arity 1, found 2"), "{arity}");

    let missing = admission_result(
        "",
        "op h : S -> S [special (id-hook HostFunctionSymbol (admission.hooked))] .",
    );
    assert!(
        missing.contains("missing op-hook `selectedSymbol`"),
        "{missing}"
    );

    let wrong_arity = admission_result(
        "",
        r#"op h : S -> S
    [special (id-hook HostFunctionSymbol (admission.hooked)
              op-hook selectedSymbol (a : ~> S)
              term-hook preferredTerm (a))] ."#,
    );
    assert!(
        wrong_arity.contains("op-hook `selectedSymbol` requires arity 1"),
        "{wrong_arity}"
    );

    let wrong_kind = admission_result(
        "op chooseT : T -> T [ctor] .",
        r#"op h : S -> S
    [special (id-hook HostFunctionSymbol (admission.hooked)
              op-hook selectedSymbol (chooseT : T ~> T)
              term-hook preferredTerm (a))] ."#,
    );
    assert!(
        wrong_kind.contains("no profile compatible with `h`"),
        "{wrong_kind}"
    );

    let missing_term = admission_result(
        "",
        r#"op h : S -> S
    [special (id-hook HostFunctionSymbol (admission.hooked)
              op-hook selectedSymbol (wrap : S ~> S))] ."#,
    );
    assert!(
        missing_term.contains("missing term-hook `preferredTerm`"),
        "{missing_term}"
    );

    let wrong_term_sort = admission_result(
        "",
        r#"op h : S -> S
    [special (id-hook HostFunctionSymbol (admission.hooked)
              op-hook selectedSymbol (wrap : S ~> S)
              term-hook preferredTerm (b))] ."#,
    );
    assert!(
        wrong_term_sort
            .contains("term-hook `preferredTerm` must resolve to a constant in the expected kind"),
        "{wrong_term_sort}"
    );

    let nonconstant = admission_result(
        "",
        r#"op h : S -> S
    [special (id-hook HostFunctionSymbol (admission.hooked)
              op-hook selectedSymbol (wrap : S ~> S)
              term-hook preferredTerm (wrap(a)))] ."#,
    );
    assert!(
        nonconstant.contains("must resolve to a constant"),
        "{nonconstant}"
    );

    let duplicate = admission_result(
        "",
        r#"op h : S -> S
    [special (id-hook HostFunctionSymbol (admission.hooked)
              op-hook selectedSymbol (wrap : S ~> S)
              op-hook selectedSymbol (wrap : S ~> S)
              term-hook preferredTerm (a))] ."#,
    );
    assert!(
        duplicate.contains("repeats hook purpose `selectedSymbol`"),
        "{duplicate}"
    );

    let unexpected = admission_result(
        "",
        r#"op h : S -> S
    [special (id-hook HostFunctionSymbol (admission.hooked)
              op-hook selectedSymbol (wrap : S ~> S)
              op-hook extraSymbol (wrap : S ~> S)
              term-hook preferredTerm (a))] ."#,
    );
    assert!(
        unexpected.contains("unexpected op-hook `extraSymbol`"),
        "{unexpected}"
    );
}

#[test]
fn zero_arity_and_compatible_overloads_use_selected_declarations() {
    let zero_calls = Arc::new(AtomicUsize::new(0));
    let functions = HostFunctionCatalog::builder()
        .register(
            "zero.result",
            ZeroReducer {
                calls: Arc::clone(&zero_calls),
            },
            StrictReducerDescriptor::builder(0)
                .require_constant_term_hook("resultTerm", HookSort::Result)
                .build(),
        )
        .expect("register zero-arity reducer")
        .register(
            "overload.echo",
            EchoSelectedRange,
            StrictReducerDescriptor::builder(1).build(),
        )
        .expect("register overload reducer")
        .register(
            "overload.other",
            EchoSelectedRange,
            StrictReducerDescriptor::builder(1).build(),
        )
        .expect("register second overload reducer")
        .register(
            "overload.binary",
            EchoSelectedRange,
            StrictReducerDescriptor::builder(2).build(),
        )
        .expect("register binary overload reducer")
        .register(
            "overload.hooked",
            EchoSelectedRange,
            StrictReducerDescriptor::builder(1)
                .require_constant_term_hook("selectedTerm", HookSort::Result)
                .build(),
        )
        .expect("register hooked overload reducer")
        .build();
    let mut session = Session::builder().host_functions(functions.clone()).build();
    let output = session
        .eval(
            r#"fmod ZERO-HOST is
  sort S .
  op answer : -> S [ctor] .
  op raw : -> S .
  op host : -> S
    [special (id-hook HostFunctionSymbol (zero.result)
              term-hook resultTerm (raw))] .
  eq raw = answer .
endfm
set trace on .
reduce in ZERO-HOST : host ."#,
            false,
        )
        .output;
    assert!(output.contains("result S: answer"), "{output}");
    assert_rewrite_counts(&output, &[2]);
    assert_eq!(zero_calls.load(Ordering::SeqCst), 1);
    assert!(
        output.contains("(strict Rust reducer zero.result for symbol host)"),
        "{output}"
    );
    assert_in_order(
        &output,
        &[
            "(strict Rust reducer zero.result for symbol host)",
            "eq raw = answer",
        ],
    );

    let overload_source = r#"fmod HOST-OVERLOAD is
  sorts A B Top .
  subsort A < Top .
  subsort B < Top .
  op a : -> A [ctor] .
  op b : -> B [ctor] .
  op echo : A -> A
    [special (id-hook HostFunctionSymbol (overload.echo))] .
  op echo : B -> B
    [special (id-hook HostFunctionSymbol (overload.echo))] .
endfm"#;
    assert_eq!(session.eval(overload_source, false).output, "");
    let a = session.eval("reduce in HOST-OVERLOAD : echo(a) .", false);
    assert!(a.output.contains("result A: a"), "{}", a.output);
    let b = session.eval("reduce in HOST-OVERLOAD : echo(b) .", false);
    assert!(b.output.contains("result B: b"), "{}", b.output);

    let separate_arities = session.eval(
        r#"fmod HOST-SEPARATE-ARITIES is
  sort S .
  op a : -> S [ctor] .
  op echo : S -> S
    [special (id-hook HostFunctionSymbol (overload.echo))] .
  op echo : S S -> S
    [special (id-hook HostFunctionSymbol (overload.binary))] .
endfm"#,
        false,
    );
    assert_eq!(separate_arities.output, "");
    for term in ["echo(a)", "echo(a, a)"] {
        let output = session
            .eval(
                &format!("reduce in HOST-SEPARATE-ARITIES : {term} ."),
                false,
            )
            .output;
        assert!(output.contains("result S: a"), "{term}: {output}");
    }

    let mut ditto = Session::builder().host_functions(functions.clone()).build();
    let shared_output = ditto.eval(
        r#"fmod HOST-DITTO-SHARED is
  sorts A B Top .
  subsort A < Top .
  subsort B < Top .
  op a : -> A [ctor] .
  op b : -> B [ctor] .
  op echo : A -> A
    [special (id-hook HostFunctionSymbol (overload.echo))] .
  op echo : B -> B [ditto] .
endfm"#,
        false,
    );
    assert_eq!(shared_output.output, "");
    let shared = ditto.eval("reduce in HOST-DITTO-SHARED : echo(b) .", false);
    assert!(shared.output.contains("result B: b"), "{}", shared.output);

    let disconnected_output = ditto.eval(
        r#"fmod HOST-DITTO-DISCONNECTED is
  sorts A B .
  op a : -> A [ctor] .
  op b : -> B [ctor] .
  op echo : A -> A
    [special (id-hook HostFunctionSymbol (overload.echo))] .
  op echo : B -> B [ditto] .
endfm"#,
        false,
    );
    assert_eq!(disconnected_output.output, "");
    let disconnected = ditto.eval("reduce in HOST-DITTO-DISCONNECTED : echo(b) .", false);
    assert!(
        disconnected.output.contains("result B: b"),
        "{}",
        disconnected.output
    );

    let changed_arity = ditto.eval(
        r#"fmod HOST-DITTO-CHANGED-ARITY is
  sort S .
  op echo : S -> S
    [special (id-hook HostFunctionSymbol (overload.echo))] .
  op echo : S S -> S [ditto] .
endfm"#,
        false,
    );
    assert!(
        changed_arity
            .output
            .contains("uses `ditto` without a preceding declaration of the same arity"),
        "{}",
        changed_arity.output
    );

    let incompatible_hook = ditto.eval(
        r#"fmod HOST-DITTO-INCOMPATIBLE-HOOK is
  sorts A B .
  op marker : -> A [ctor] .
  op echo : A -> A
    [special (id-hook HostFunctionSymbol (overload.hooked)
              term-hook selectedTerm (marker))] .
  op echo : B -> B [ditto] .
endfm"#,
        false,
    );
    assert!(
        incompatible_hook
            .output
            .contains("term-hook `selectedTerm` must resolve to a constant in the expected kind"),
        "{}",
        incompatible_hook.output
    );

    for (first, second) in [
        ("overload.echo", "overload.other"),
        ("overload.other", "overload.echo"),
    ] {
        let mut inconsistent = Session::builder().host_functions(functions.clone()).build();
        let source = format!(
            r#"fmod HOST-INCONSISTENT is
  sorts A B .
  op echo : A -> A
    [special (id-hook HostFunctionSymbol ({first}))] .
  op echo : B -> B
    [special (id-hook HostFunctionSymbol ({second}))] .
endfm"#
        );
        let output = inconsistent.eval(&source, false).output;
        assert!(
            output.contains("inconsistent overload bindings"),
            "{output}"
        );
    }

    let mut incompatible_profiles = Session::builder().host_functions(functions.clone()).build();
    let output = incompatible_profiles
        .eval(
            r#"fmod HOST-INCOMPATIBLE-PROFILES is
  sorts D R1 R2 K .
  subsorts D R1 R2 < K .
  op echo : K -> R1
    [special (id-hook HostFunctionSymbol (overload.echo))] .
  op echo : D -> R2
    [special (id-hook HostFunctionSymbol (overload.echo))] .
endfm"#,
            false,
        )
        .output;
    assert!(
        output.contains("overlapping declarations with incomparable result sorts"),
        "{output}"
    );

    let output = incompatible_profiles
        .eval(
            r#"fmod HOST-INCOMPATIBLE-STRUCTURE is
  sort S .
  op echo : S S -> S
    [special (id-hook HostFunctionSymbol (overload.binary))] .
  op echo : S S -> S
    [assoc special (id-hook HostFunctionSymbol (overload.binary))] .
endfm"#,
            false,
        )
        .output;
    assert!(
        output.contains("inconsistent structural declarations"),
        "{output}"
    );

    let mut missing = Session::builder().host_functions(functions).build();
    for source in [
        r#"fmod HOST-MISSING-OVERLOAD-FIRST is
  sorts A B .
  op echo : A -> A
    [special (id-hook HostFunctionSymbol (overload.echo))] .
  op echo : B -> B .
endfm"#,
        r#"fmod HOST-MISSING-OVERLOAD-LAST is
  sorts A B .
  op echo : A -> A .
  op echo : B -> B
    [special (id-hook HostFunctionSymbol (overload.echo))] .
endfm"#,
    ] {
        let output = missing.eval(source, false).output;
        assert!(
            output.contains("no matching HostFunctionSymbol attachment"),
            "{output}"
        );
    }
}

fn configured_meta_session() -> Session {
    let mut session = configured_session();
    let prelude = session.eval(
        include_str!("../../../conformance/prelude-meta.maude"),
        false,
    );
    assert!(
        !prelude.output.contains("error in module") && !prelude.output.contains("parse error"),
        "META-LEVEL prelude: {}",
        prelude.output
    );
    let interpreter = session.eval(
        include_str!("../../../share/maude-gpl/metaInterpreter.maude"),
        false,
    );
    assert!(
        !interpreter.output.contains("error in module")
            && !interpreter.output.contains("parse error"),
        "META-INTERPRETER: {}",
        interpreter.output
    );
    session
}

#[test]
fn configured_meta_descent_and_child_interpreter_reuse_catalog() {
    let mut session = configured_meta_session();
    for source in [HOST_SCALARS_FIXTURE, ROUTING_FIXTURE] {
        let loaded = session.eval(source, false);
        assert_eq!(loaded.output, "", "{loaded:?}");
    }
    let modules = session.eval(
        r#"set include BOOL off .
fmod NESTED-HOST is
  sorts Color Decision .
  ops blue green : -> Color [ctor] .
  op picked : Color -> Decision [ctor] .
  op choose : Color Color -> Decision
    [special (id-hook HostFunctionSymbol (routing.prefer-configured)
              op-hook selectedSymbol (picked : Color ~> Decision)
              term-hook preferredTerm (blue))] .
endfm
fmod NESTED-HOST-FAULT is
  sort Elt .
  op a : -> Elt [ctor] .
  op fail : Elt -> Elt
    [special (id-hook HostFunctionSymbol (testing.fail))] .
endfm
fmod REFLECTED-IDENTITY-FAULT is
  sort Elt .
  op a : -> Elt [ctor] .
  op fail : Elt -> Elt
    [special (id-hook HostFunctionSymbol (testing.fail))] .
  op guard : Elt -> Elt [strat (0 1)] .
  op _+_ : Elt Elt -> Elt [assoc comm id: guard(fail(a))] .
  var X : Elt .
  eq guard(X) = a .
endfm
fmod REFLECTED-HOST-REBUILD is
  protecting META-LEVEL .
  op rebuild : Qid Module -> Module .
  vars SOURCE TARGET : Qid .
  var IMPORTS : ImportList .
  var SORTS : SortSet .
  var SUBSORTS : SubsortDeclSet .
  var OPS : OpDeclSet .
  var MBS : MembAxSet .
  var EQS : EquationSet .
  eq rebuild(TARGET,
       fmod SOURCE is IMPORTS sorts SORTS . SUBSORTS OPS MBS EQS endfm)
    = fmod TARGET is IMPORTS sorts SORTS . SUBSORTS OPS MBS EQS endfm .
endfm
mod CHILD-HOST-SUCCESS is
  protecting META-INTERPRETER .
  sort HostPhase .
  ops start scalar-unary scalar-binary routing-install routing : -> HostPhase [ctor] .
  op me : -> Oid .
  op User : -> Cid .
  op phase:_ : HostPhase -> Attribute .
  op unary:_ : Msg -> Attribute .
  op binary:_ : Msg -> Attribute .
  op routed:_ : Msg -> Attribute .
  vars X Y Z : Oid .
  var AS : AttributeSet .
  var N : RewriteCount .
  var T : Term .
  var TY : Type .
  rl < X : User | phase: start, AS > createdInterpreter(X, Y, Z) =>
     < X : User | phase: start, AS >
       insertModule(Z, X, upModule('HOST-SCALARS-RENAMED, false)) .
  rl < X : User | phase: start, AS > insertedModule(X, Y) =>
     < X : User | phase: scalar-unary, AS >
       reduceTerm(Y, X, 'HOST-SCALARS-RENAMED, 'slug['rawTag.String]) .
  rl < X : User | phase: scalar-unary, AS > reducedTerm(X, Y, N, T, TY) =>
     < X : User | phase: scalar-binary,
                    unary: reducedTerm(X, Y, N, T, TY), AS >
       reduceTerm(Y, X, 'HOST-SCALARS-RENAMED,
         '_join_['leftPart.String, 'rightPart.String]) .
  rl < X : User | phase: scalar-binary, AS > reducedTerm(X, Y, N, T, TY) =>
     < X : User | phase: routing-install,
                    binary: reducedTerm(X, Y, N, T, TY), AS >
       insertModule(Y, X, upModule('COLOR-ROUTING-RENAMED, false)) .
  rl < X : User | phase: routing-install, AS > insertedModule(X, Y) =>
     < X : User | phase: routing, AS >
       reduceTerm(Y, X, 'COLOR-ROUTING-RENAMED,
         'choose['red.Color, 'green.Color]) .
  rl < X : User | phase: routing, AS > reducedTerm(X, Y, N, T, TY) =>
     < X : User | phase: routing,
                    routed: reducedTerm(X, Y, N, T, TY), AS >
       quit(Y, X) .
endm
mod CHILD-HOST-FAULT is
  protecting META-INTERPRETER .
  op me2 : -> Oid .
  op FaultUser : -> Cid .
  vars X Y Z : Oid .
  var AS : AttributeSet .
  rl < X : FaultUser | AS > createdInterpreter(X, Y, Z) =>
     < X : FaultUser | AS >
       insertModule(Z, X, upModule('NESTED-HOST-FAULT, true)) .
  rl < X : FaultUser | AS > insertedModule(X, Y) =>
     < X : FaultUser | AS >
       reduceTerm(Y, X, 'NESTED-HOST-FAULT, 'fail['a.Elt]) .
endm"#,
        false,
    );
    assert!(
        !modules.output.contains("error in module") && !modules.output.contains("parse error"),
        "{}",
        modules.output
    );
    // The source build succeeds because guard's top-first equation removes the faulting identity
    // subterm. upModule's statement-free home shell removes that equation; its configured rebuild must
    // propagate the original identity reducer fault rather than treating a failed `.ok()` as no result.
    let reflected_identity_fault = session.eval(
        "reduce in META-LEVEL : upModule('REFLECTED-IDENTITY-FAULT, false) .",
        false,
    );
    assert_eq!(
        reflected_identity_fault.output,
        "error: strict reducer `testing.fail` failed: deliberate fixture fault"
    );
    assert!(
        session
            .eval("continue .", false)
            .output
            .contains("error: no previous rewriting")
    );

    let reflected = session.eval(
        "reduce in META-LEVEL : metaReduce(upModule('NESTED-HOST, false), 'choose['blue.Color, 'blue.Color]) .",
        false,
    );
    assert!(
        reflected.output.contains("'picked['blue.Color]"),
        "{}",
        reflected.output
    );

    // Changing the reflected header defeats the source-backed upModule cache and forces generic
    // downModule reconstruction. All three paths require the configured catalog: host success, decline
    // to an ordinary equation, and decline to the owise fallback.
    let rebuilt = session.eval(
        r#"reduce in REFLECTED-HOST-REBUILD : metaReduce(
  rebuild('HOST-SCALARS-REBUILT, upModule('HOST-SCALARS, false)),
  'normalizeTag['rawTag.String]) .
reduce in REFLECTED-HOST-REBUILD : metaReduce(
  rebuild('HOST-SCALARS-REBUILT, upModule('HOST-SCALARS, false)),
  'normalizeTag['ordinary.String]) .
reduce in REFLECTED-HOST-REBUILD : metaReduce(
  rebuild('HOST-SCALARS-REBUILT, upModule('HOST-SCALARS, false)),
  'normalizeTag['opaque.String]) ."#,
        false,
    );
    for expected in [
        "\"tnk-reducers\"",
        "\"ordinary-equation\"",
        "\"opaque-fallback\"",
    ] {
        assert!(rebuilt.output.contains(expected), "{}", rebuilt.output);
    }
    assert!(
        !rebuilt.output.contains("missing host capability"),
        "{}",
        rebuilt.output
    );

    let canonical_reflected = session.eval(
        r#"reduce in META-LEVEL : metaReduce(
  upModule('HOST-SCALARS-RENAMED, false), 'slug['rawTag.String]) .
reduce in META-LEVEL : metaReduce(
  upModule('HOST-SCALARS-RENAMED, false),
  '_join_['leftPart.String, 'rightPart.String]) .
reduce in META-LEVEL : metaReduce(
  upModule('COLOR-ROUTING-RENAMED, false),
  'choose['red.Color, 'green.Color]) ."#,
        false,
    );
    assert!(
        canonical_reflected.output.contains("\"tnk-reducers\""),
        "{}",
        canonical_reflected.output
    );
    assert!(
        canonical_reflected.output.contains("\"api/v1\""),
        "{}",
        canonical_reflected.output
    );
    assert!(
        canonical_reflected.output.contains("'none."),
        "{}",
        canonical_reflected.output
    );
    assert!(
        !canonical_reflected
            .output
            .contains("missing host capability"),
        "{}",
        canonical_reflected.output
    );

    let reflected_fault = session.eval(
        r#"reduce in REFLECTED-HOST-REBUILD : metaReduce(
  rebuild('NESTED-HOST-FAULT-REBUILT, upModule('NESTED-HOST-FAULT, false)),
  'fail['a.Elt]) ."#,
        false,
    );
    assert_eq!(
        reflected_fault.output,
        "error: strict reducer `testing.fail` failed: deliberate fixture fault"
    );
    assert!(
        session
            .eval("continue .", false)
            .output
            .contains("error: no previous rewriting")
    );

    let child = session.eval(
        r#"erewrite in CHILD-HOST-SUCCESS :
  <> < me : User | phase: start >
  createInterpreter(interpreterManager, me, none) ."#,
        false,
    );
    assert!(
        child.output.contains("\"tnk-reducers\""),
        "{}",
        child.output
    );
    assert!(child.output.contains("\"api/v1\""), "{}", child.output);
    assert!(child.output.contains("'none."), "{}", child.output);
    assert!(
        child
            .output
            .matches("reducedTerm(me, interpreter(0), 2")
            .count()
            >= 2,
        "{}",
        child.output
    );
    assert!(
        child.output.contains("reducedTerm(me, interpreter(0), 3"),
        "{}",
        child.output
    );

    let child_fault = session.eval(
        r#"erewrite in CHILD-HOST-FAULT :
  <> < me2 : FaultUser | none >
  createInterpreter(interpreterManager, me2, none) ."#,
        false,
    );
    assert_eq!(
        child_fault.output,
        "error: strict reducer `testing.fail` failed: deliberate fixture fault"
    );
    assert!(
        session
            .eval("continue .", false)
            .output
            .contains("error: no previous rewriting")
    );
}

#[test]
fn hook_references_follow_qualified_operator_and_sort_renaming() {
    let mut session = configured_session();
    let output = session
        .eval(
            r#"fmod HOOK-RENAME-SOURCE is
  sorts Color Decision .
  ops preferred other : -> Color [ctor] .
  op selected : Color -> Decision [ctor] .
  op choose : Color Color -> Decision
    [special (id-hook HostFunctionSymbol (routing.prefer-configured)
              op-hook selectedSymbol (selected : Color ~> Decision)
              term-hook preferredTerm (preferred))] .
endfm
fmod HOOK-RENAME-EXTRA is
  sort Extra .
  op extra : -> Extra [ctor] .
endfm
fmod HOOK-RENAME-SUM is
  protecting HOOK-RENAME-SOURCE + HOOK-RENAME-EXTRA .
endfm
fmod HOOK-RENAME-TARGET is
  protecting HOOK-RENAME-SOURCE * (
    sort Color to Shade,
    sort Decision to Choice,
    op preferred to favorite,
    op selected : Color -> Decision to chosen,
    op choose : Color Color -> Decision to route
  ) .
endfm
set trace on .
reduce in HOOK-RENAME-SUM : choose(preferred, other) .
reduce in HOOK-RENAME-TARGET : route(X:Shade, other) ."#,
            false,
        )
        .output;
    assert!(
        output.contains("result Decision: selected(preferred)"),
        "{output}"
    );
    assert!(output.contains("result Choice: chosen(other)"), "{output}");
    assert_rewrite_counts(&output, &[1, 1]);
    assert!(output.contains("routing.prefer-configured"), "{output}");
    assert!(output.contains("symbol route"), "{output}");
}

#[test]
fn overloaded_hook_profiles_must_resolve_to_one_binding() {
    let descriptor = StrictReducerDescriptor::builder(1)
        .require_op_hook("selectedSymbol", &[HookSort::Argument(0)], HookSort::Result)
        .build();
    let functions = HostFunctionCatalog::builder()
        .register("overload.hooked", EchoSelectedRange, descriptor)
        .expect("register hooked overload reducer")
        .build();

    let mut compatible = Session::builder().host_functions(functions.clone()).build();
    let accepted = compatible.eval(
        r#"fmod HOOKED-OVERLOAD is
  sorts A B Top .
  subsort A < Top .
  subsort B < Top .
  ops a : -> A .
  ops b : -> B .
  op picked : A -> A [ctor] .
  op picked : B -> B [ctor] .
  op host : A -> A
    [special (id-hook HostFunctionSymbol (overload.hooked)
              op-hook selectedSymbol (picked : A ~> A))] .
  op host : B -> B
    [special (id-hook HostFunctionSymbol (overload.hooked)
              op-hook selectedSymbol (picked : B ~> B))] .
endfm"#,
        false,
    );
    assert_eq!(accepted.output, "");
    assert!(
        compatible
            .eval("reduce in HOOKED-OVERLOAD : host(a) .", false)
            .output
            .contains("result A: a")
    );
    assert!(
        compatible
            .eval("reduce in HOOKED-OVERLOAD : host(b) .", false)
            .output
            .contains("result B: b")
    );

    for (first, second) in [("pickedA", "pickedB"), ("pickedB", "pickedA")] {
        let mut inconsistent = Session::builder().host_functions(functions.clone()).build();
        let source = format!(
            r#"fmod HOOKED-OVERLOAD-BAD is
  sorts A B Top .
  subsort A < Top .
  subsort B < Top .
  op pickedA : A -> A [ctor] .
  op pickedA : B -> B [ctor] .
  op pickedB : A -> A [ctor] .
  op pickedB : B -> B [ctor] .
  op host : A -> A
    [special (id-hook HostFunctionSymbol (overload.hooked)
              op-hook selectedSymbol ({first} : A ~> A))] .
  op host : B -> B
    [special (id-hook HostFunctionSymbol (overload.hooked)
              op-hook selectedSymbol ({second} : B ~> B))] .
endfm"#
        );
        let output = inconsistent.eval(&source, false).output;
        assert!(
            output.contains("inconsistent overload bindings"),
            "{output}"
        );
    }
}
