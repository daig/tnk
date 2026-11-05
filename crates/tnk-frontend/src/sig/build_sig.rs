//! Build a `tnk-core` [`Engine`] from a [`PreModule`] while recording frontend
//! syntax and name-resolution tables. Kernel invariants force the order: close sorts; declare every
//! operator and syntax profile; resolve built-in anchor symbols; then attach constructor, strategy,
//! frozen, object-role, and `special` attributes. Statements remain raw until the module grammar exists.

use crate::lex::{Frag, Interner, Sym, TokKind, Token, is_punct, split_mixfix};
use crate::sig::syntax::{BuiltModule, IdentitySpec, OpProfile, PendingHostBinding, SymbolSyntax};
use crate::surface::ast::{Attrs, IdSide, PreModule, SpecialSpec};
use std::collections::{HashMap, HashSet};
use tnk_core::engine::Engine;
use tnk_core::host::{
    HookSort, HostFunctionCatalog, HostFunctionKey, ResolvedHostHooks, StrictReducerDescriptor,
};
use tnk_core::ltl::TemporalHooks;
use tnk_core::smt::{SmtOp, SmtType};
use tnk_core::sort::{KindId, SortId};
use tnk_core::symbol::{
    BoolHooks, CharClass, ConvOp, FltOp, MetaHooks, MetaOp, ModelCheckerHooks, NatHooks, NumOp,
    QidOp, SatSolverHooks, SpecialOp, StdStream, StrOp, SymbolId,
};

type R<T> = Result<T, String>;

#[derive(Clone, Copy)]
struct EffectiveAxioms {
    assoc: bool,
    comm: bool,
    idem: bool,
    iter: bool,
    identity: bool,
    id_side: IdSide,
}

impl EffectiveAxioms {
    /// Validate structural attributes against operator arity and connected components before choosing a
    /// theory-specific representation. `None` denotes a polymorphic position.
    fn for_profile(attrs: &Attrs, domain: &[Option<KindId>], range: Option<KindId>) -> Self {
        fn same_component_or_all_polymorphic(kinds: &[Option<KindId>]) -> bool {
            if kinds.iter().all(Option::is_none) {
                return true;
            }
            let Some(first) = kinds.first().copied().flatten() else {
                return false;
            };
            kinds.iter().all(|kind| *kind == Some(first))
        }

        fn same_component_or_both_polymorphic(left: Option<KindId>, right: Option<KindId>) -> bool {
            matches!((left, right), (None, None))
                || matches!((left, right), (Some(a), Some(b)) if a == b)
        }

        let arity = domain.len();
        let mut effective = EffectiveAxioms {
            assoc: attrs.assoc,
            comm: attrs.comm,
            idem: attrs.idem,
            iter: attrs.iter,
            identity: attrs.id.is_some(),
            id_side: attrs.id_side,
        };

        effective.iter =
            effective.iter && arity == 1 && same_component_or_all_polymorphic(&[domain[0], range]);
        effective.assoc = effective.assoc
            && arity == 2
            && same_component_or_all_polymorphic(&[domain[0], domain[1], range]);
        effective.comm = effective.comm
            && arity == 2
            && same_component_or_all_polymorphic(&[domain[0], domain[1]]);
        effective.idem = effective.idem
            && arity == 2
            && same_component_or_all_polymorphic(&[domain[0], domain[1], range]);

        if effective.identity {
            if arity != 2 {
                effective.identity = false;
            } else {
                // Commutativity makes either one-sided declaration an implicit identity on both sides.
                let check_left = matches!(attrs.id_side, IdSide::Both | IdSide::Left)
                    || (attrs.id_side == IdSide::Right && effective.comm);
                let check_right = matches!(attrs.id_side, IdSide::Both | IdSide::Right)
                    || (attrs.id_side == IdSide::Left && effective.comm);
                let left_ok =
                    domain[0].is_some() && same_component_or_both_polymorphic(domain[1], range);
                let right_ok =
                    domain[1].is_some() && same_component_or_both_polymorphic(domain[0], range);
                effective.identity = (!check_left || left_ok) && (!check_right || right_ok);
                if effective.identity && effective.comm {
                    effective.id_side = IdSide::Both;
                }
            }
        }
        effective
    }
}

#[derive(Clone, PartialEq, Eq)]
struct ConstructorAxiomProfile {
    assoc: bool,
    comm: bool,
    idem: bool,
    iter: bool,
    identity: Option<(IdSide, Vec<Sym>)>,
}

impl ConstructorAxiomProfile {
    fn from_attrs(attrs: &Attrs, effective: EffectiveAxioms) -> Self {
        Self {
            assoc: effective.assoc,
            comm: effective.comm,
            idem: effective.idem,
            iter: effective.iter,
            identity: effective.identity.then(|| {
                (
                    effective.id_side,
                    attrs
                        .id
                        .as_ref()
                        .expect("an effective identity has source tokens")
                        .iter()
                        .map(|token| token.sym)
                        .collect(),
                )
            }),
        }
    }
}

/// Canonical mixfix name. Source blanks become backquotes, punctuation fragments glue, and outer
/// parentheses used to quote keyword-like names are stripped.
pub fn canonical_name(name: &[Token], i: &Interner) -> String {
    let mut out = String::new();
    let mut previous = None;
    for token in strip_outer_parens(name, i) {
        let text = i.resolve(token.sym);
        if previous.is_some_and(|left: &str| {
            let left = left.chars().next_back().expect("non-empty token");
            let right = text.chars().next().expect("non-empty token");
            !matches!(left, '_' | ':')
                && !is_punct(left)
                && !matches!(right, '_' | ':')
                && !is_punct(right)
        }) {
            out.push('`');
        }
        out.push_str(text);
        previous = Some(text);
    }
    out
}

/// The inner tokens if `toks` is wrapped in a single balanced `( … )` pair, else `toks` unchanged. The
/// opening paren must match the *final* token (depth returns to 0 only at the end), so a name that merely
/// starts and ends with parens — `(a) b (c)` — is left intact.
pub(crate) fn strip_outer_parens<'a>(toks: &'a [Token], i: &Interner) -> &'a [Token] {
    if toks.len() < 2 || i.resolve(toks[0].sym) != "(" || i.resolve(toks[toks.len() - 1].sym) != ")"
    {
        return toks;
    }
    let mut depth = 0i32;
    for (k, t) in toks.iter().enumerate() {
        match i.resolve(t.sym) {
            "(" => depth += 1,
            ")" => depth -= 1,
            _ => {}
        }
        if depth == 0 && k + 1 != toks.len() {
            return toks; // closed before the end → not a single enclosing wrapper
        }
    }
    &toks[1..toks.len() - 1]
}

/// Resolve a sort name, including the kind form `[S]`, which denotes the error sort of S's connected
/// component. Plain names use direct lookup. Kind resolution requires closed sorts, so callers use this
/// for operator profiles and variables after subsorts have been resolved.
fn resolve_sort(engine: &Engine, sorts: &HashMap<String, SortId>, name: &str) -> R<SortId> {
    if let Some(inner) = name.strip_prefix('[').and_then(|s| s.strip_suffix(']')) {
        // A bracket can contain one sort (`[S]`) or several (`[A, B]`) naming the same connected
        // component. Resolve the first complete sort name; depth-aware splitting keeps a structured sort
        // such as `Map{X,Y}` intact.
        let first = first_kind_component(inner);
        let inner_id = sorts
            .get(first)
            .copied()
            .ok_or_else(|| format!("unknown sort `{first}` in kind `[{inner}]`"))?;
        Ok(engine.sorts().error_sort(engine.sorts().kind_of(inner_id)))
    } else {
        sorts
            .get(name)
            .copied()
            .ok_or_else(|| format!("unknown sort `{name}`"))
    }
}

/// The first comma-separated sort of a multi-sort kind bracket's inner text, respecting `{ … }` / `[ … ]`
/// nesting so a structured sort (`Map{X,Y}`) is not split at its inner `,`. `[A,B]` → `A`; `[Map{X,Y}]`
/// → `Map{X,Y}`.
pub fn first_kind_component(inner: &str) -> &str {
    let mut depth = 0i32;
    for (idx, c) in inner.char_indices() {
        match c {
            '{' | '[' => depth += 1,
            '}' | ']' => depth -= 1,
            ',' if depth == 0 => return &inner[..idx],
            _ => {}
        }
    }
    inner
}

fn strict_eager_source_strategy(raw: &[u32], arity: usize) -> bool {
    if raw.is_empty() {
        return true;
    }
    let arguments = if raw.last() == Some(&0) {
        &raw[..raw.len() - 1]
    } else {
        raw
    };
    arguments.len() == arity
        && arguments
            .iter()
            .enumerate()
            .all(|(position, &step)| step as usize == position + 1)
}

pub fn build_module(pm: &PreModule, interner: &mut Interner) -> R<BuiltModule> {
    build_module_with_host_functions(pm, interner, &HostFunctionCatalog::default())
}

/// Build a module against an immutable host-function capability catalog.
pub(crate) fn build_module_with_host_functions(
    pm: &PreModule,
    interner: &mut Interner,
    host_functions: &HostFunctionCatalog,
) -> R<BuiltModule> {
    let mut engine = Engine::with_host_functions(host_functions.clone());
    let mut sorts: HashMap<String, SortId> = HashMap::new();

    // 1. Sorts + subsorts, then close.
    for name in &pm.sorts {
        let id = engine.add_sort(name.clone());
        sorts.insert(name.clone(), id);
    }
    let sort_id = |sorts: &HashMap<String, SortId>, name: &str| -> R<SortId> {
        sorts
            .get(name)
            .copied()
            .ok_or_else(|| format!("unknown sort `{name}`"))
    };
    for chain in &pm.subsorts {
        for w in chain.windows(2) {
            for sub in &w[0] {
                for sup in &w[1] {
                    engine.add_subsort(sort_id(&sorts, sub)?, sort_id(&sorts, sup)?);
                }
            }
        }
    }
    // TNK-SORT-001: a subsort cycle invalidates the signature. The PreModule here is already
    // flattened, so this also catches cycles formed only across imports. Rejecting before closure
    // keeps the module definition atomic (nothing is installed) and avoids the closure's panic.
    if let Some(cycle) = engine.subsort_cycle() {
        let path = cycle
            .iter()
            .map(|&s| engine.sorts().name(s))
            .collect::<Vec<_>>()
            .join(" < ");
        return Err(format!("subsort declarations form a cycle: `{path}`"));
    }
    engine.close_sorts();

    let mut ops: HashMap<(String, usize), SymbolId> = HashMap::new();
    let mut name_to_sym: HashMap<String, SymbolId> = HashMap::new();
    let mut syntax: HashMap<SymbolId, SymbolSyntax> = HashMap::new();
    let mut op_profiles: Vec<OpProfile> = Vec::new();
    // Symbol identity is the **kind profile**: name plus domain and range connected components.
    // Subsort overloads in the same components, such as `_+_ : NzNat Nat -> NzNat` and
    // `_+_ : Nat Nat -> Nat`, share a symbol. Ad-hoc overloads across components, such as
    // `wrap : Hue -> Box{ToColor}` and `wrap : Box{ToColor} -> Box{V}`, produce distinct symbols.
    // The argument kind selects the declaration group.
    let mut sym_by_profile: HashMap<(String, Vec<KindId>, KindId), SymbolId> = HashMap::new();
    // Each source declaration maps to its kernel symbol(s): one for an ordinary op, or — for a
    // `poly`/`Universal` op — one per kind (the per-kind expansion below). Later passes iterate it by the
    // source index, so it is pre-sized and each declaration stores at its own index (the loop below may
    // visit the entries out of source order — constants first, see next).
    let mut op_syms: Vec<Vec<SymbolId>> = vec![Vec::new(); pm.ops.len()];
    let mut decl_profiles: Vec<Vec<OpProfile>> = vec![Vec::new(); pm.ops.len()];
    // Identity bubbles are parsed only after the per-module grammar exists.
    let mut identity_specs: Vec<IdentitySpec> = Vec::new();
    // Structural constructor axioms belong to each source overload, while the kernel executes one
    // folded Symbol theory. Retain the first profile long enough to mark disagreements before folding.
    let mut constructor_axiom_profiles: HashMap<SymbolId, ConstructorAxiomProfile> = HashMap::new();
    let mut constructor_flags: HashMap<SymbolId, bool> = HashMap::new();

    // Declare every operator and expand each polymorphic declaration eagerly over all kinds after sort
    // closure. Listed positions use that kind's error sort; `Universal` never reaches ordinary sort
    // lookup.
    //
    // Partition constants before nonconstants to preserve symbol-index ordering. The later identity
    // attachment pass resolves forward and compound identity references.
    let mut decl_order: Vec<usize> = (0..pm.ops.len()).collect();
    decl_order.sort_by_key(|&idx| !pm.ops[idx].domain.is_empty());
    for &idx in &decl_order {
        let od = &pm.ops[idx];
        let cname = canonical_name(&od.name, interner);
        let arity = od.domain.len();
        // Validate semantic attributes before selecting a theory-specific symbol. The raw attributes stay
        // on `od.attrs` for surface rendering; only the effective attributes below control compiled syntax,
        // identity attachment, and kernel theory selection.

        // The (domain, range) profile(s) this declaration expands to.
        let mut profiles: Vec<(Vec<SortId>, SortId)> = match &od.attrs.poly {
            None => {
                let domain: Vec<SortId> = od
                    .domain
                    .iter()
                    .map(|s| resolve_sort(&engine, &sorts, s))
                    .collect::<R<_>>()?;
                vec![(domain, resolve_sort(&engine, &sorts, &od.range)?)]
            }
            Some(poly) => {
                let s = engine.sorts();
                let err_sorts: Vec<SortId> = s.kinds().map(|k| s.error_sort(k)).collect();
                err_sorts
                    .into_iter()
                    .map(|err| {
                        // poly position → this kind's error sort; otherwise the declared sort.
                        let domain: Vec<SortId> = od
                            .domain
                            .iter()
                            .enumerate()
                            .map(|(i, sn)| {
                                if poly.contains(&(i as u32 + 1)) {
                                    Ok(err)
                                } else {
                                    sort_id(&sorts, sn)
                                }
                            })
                            .collect::<R<_>>()?;
                        let range = if poly.contains(&0) {
                            err
                        } else {
                            sort_id(&sorts, &od.range)?
                        };
                        Ok((domain, range))
                    })
                    .collect::<R<_>>()?
            }
        };

        // Partial declarations are kind-level in every position, so they accept kind-level arguments and
        // may produce an undefined result at the result kind.
        if od.partial {
            for (domain, range) in profiles.iter_mut() {
                for sort in domain {
                    *sort = engine.sorts().error_sort(engine.sorts().kind_of(*sort));
                }
                *range = engine.sorts().error_sort(engine.sorts().kind_of(*range));
            }
        }

        // Validate structural attributes against the pre-expansion profile, where polymorphic positions
        // remain absent. Per-instance validation would retain attributes inconsistently.
        let first_profile = profiles
            .first()
            .expect("an operator declaration produces at least one profile");
        let poly = od.attrs.poly.as_deref().unwrap_or(&[]);
        let declared_domain_kinds: Vec<Option<KindId>> = first_profile
            .0
            .iter()
            .enumerate()
            .map(|(position, &sort)| {
                (!poly.contains(&(position as u32 + 1))).then(|| engine.sorts().kind_of(sort))
            })
            .collect();
        let declared_range_kind =
            (!poly.contains(&0)).then(|| engine.sorts().kind_of(first_profile.1));
        let effective =
            EffectiveAxioms::for_profile(&od.attrs, &declared_domain_kinds, declared_range_kind);

        let mut decl_syms: Vec<SymbolId> = Vec::with_capacity(profiles.len());
        for (domain, range) in profiles {
            let dom_kinds: Vec<KindId> =
                domain.iter().map(|&s| engine.sorts().kind_of(s)).collect();
            let profile = (cname.clone(), dom_kinds, engine.sorts().kind_of(range));

            let sym = if let Some(&existing) = sym_by_profile.get(&profile) {
                let inherited = od.attrs.ditto;
                let ctor = if inherited {
                    constructor_flags.get(&existing).copied().unwrap_or(false)
                } else {
                    od.attrs.ctor
                };
                let incoming = ConstructorAxiomProfile::from_attrs(&od.attrs, effective);
                if !inherited
                    && constructor_axiom_profiles
                        .get(&existing)
                        .is_some_and(|first| first != &incoming)
                {
                    engine.mark_inconsistent_constructor_axioms(existing);
                }
                engine.add_op_decl_with_ctor(existing, domain.clone(), range, ctor);
                constructor_flags.insert(existing, ctor);
                existing
            } else {
                let sym = declare_op(&mut engine, &cname, &od.attrs, effective, &domain, range);
                constructor_axiom_profiles.insert(
                    sym,
                    ConstructorAxiomProfile::from_attrs(&od.attrs, effective),
                );
                constructor_flags.insert(sym, od.attrs.ctor);
                sym_by_profile.insert(profile, sym);
                ops.entry((cname.clone(), arity)).or_insert(sym); // first symbol of this (name, arity)
                name_to_sym.entry(cname.clone()).or_insert(sym);
                let object_attribute = cname.ends_with(":_")
                    && engine.sorts().name(range) == "Attribute"
                    && od.attrs.ctor;
                // A zero-arity name whose one declaration token contains `:` is a literal constant
                // (for example, escaped `marker:tag`), not the spaced colon syntax of object attributes.
                let source_name = strip_outer_parens(&od.name, interner);
                let literal_colon_constant = arity == 0
                    && source_name.len() == 1
                    && source_name
                        .first()
                        .is_some_and(|token| interner.resolve(token.sym).contains(':'));
                let mut frags = if literal_colon_constant {
                    vec![Frag::Tok(interner.intern(&cname))]
                } else {
                    split_mixfix(&cname, interner)
                };
                let holes = frags.iter().filter(|f| matches!(f, Frag::Hole)).count();
                let mut prec = od.attrs.prec;
                let mut gather = od.attrs.gather.clone();
                let mut format = od.attrs.format.clone();
                if holes != 0 && holes != domain.len() {
                    // A mismatched hole count leaves the declaration available in prefix form and clears
                    // attributes that apply only to valid mixfix syntax.
                    frags = vec![Frag::Tok(interner.intern(&cname))];
                    prec = None;
                    gather = None;
                    format = None;
                }
                syntax.insert(
                    sym,
                    SymbolSyntax {
                        frags,
                        domain: domain.clone(),
                        range,
                        prec,
                        gather,
                        object_attribute,
                        spaced_label_colon: object_attribute && od.name.len() > 1,
                        assoc: effective.assoc,
                        iter: effective.iter,
                        format,
                    },
                );
                sym
            };
            let op_profile = OpProfile {
                symbol: sym,
                domain: domain.clone(),
                range,
            };
            op_profiles.push(op_profile.clone());
            decl_profiles[idx].push(op_profile);
            if effective.identity
                && let Some(tokens) = &od.attrs.id
                && !identity_specs.iter().any(|spec| spec.symbol == sym)
            {
                match effective.id_side {
                    crate::surface::ast::IdSide::Both => engine.reserve_identity(sym, range),
                    crate::surface::ast::IdSide::Left => {
                        engine.reserve_one_sided_identity(
                            sym,
                            tnk_core::symbol::IdentitySide::Left,
                            range,
                        );
                    }
                    crate::surface::ast::IdSide::Right => {
                        engine.reserve_one_sided_identity(
                            sym,
                            tnk_core::symbol::IdentitySide::Right,
                            range,
                        );
                    }
                }
                identity_specs.push(IdentitySpec {
                    symbol: sym,
                    sort: range,
                    side: effective.id_side,
                    tokens: tokens.clone(),
                });
            }
            decl_syms.push(sym);
        }
        op_syms[idx] = decl_syms;
    }

    // Record the built-in anchors after every name resolves.
    let mut nat_succ = None;
    let mut nat_zero = None;
    let mut string_sym = None;
    let mut float_sym = None;
    let mut qid_sym = None;
    let mut minus_sym = None;
    let mut division_sym = None;
    let mut true_sym = None;
    let mut false_sym = None;
    let mut succ_zero: HashMap<SymbolId, SymbolId> = HashMap::new();
    for (idx, od) in pm.ops.iter().enumerate() {
        let Some(spec) = &od.attrs.special else {
            continue;
        };
        let Some((class, data)) = &spec.id_hook else {
            continue;
        };
        let sym = op_syms[idx][0]; // anchors are concrete (non-poly) ⇒ exactly one instance
        match class.as_str() {
            "SuccSymbol" => {
                nat_succ = Some(sym);
                let proposed = term_hook_sym(spec, "zeroTerm", &name_to_sym, interner)
                    .ok_or("SuccSymbol missing its zeroTerm")?;
                let zero = engine.register_succ_zero(sym, proposed);
                nat_zero = Some(zero);
                succ_zero.insert(sym, zero);
            }
            "StringSymbol" => string_sym = Some(sym),
            "FloatSymbol" => float_sym = Some(sym),
            "QuotedIdentifierSymbol" => qid_sym = Some(sym),
            "MinusSymbol" => minus_sym = Some(sym),
            "DivisionSymbol" => division_sym = Some(sym),
            "SystemTrue" => true_sym = Some(sym),
            "SystemFalse" => false_sym = Some(sym),
            "SMT_NumberSymbol" => {
                let kind = match data.first().map(String::as_str) {
                    Some("integers") => SmtType::Integer,
                    Some("reals") => SmtType::Real,
                    _ => return Err("SMT_NumberSymbol needs `integers` or `reals`".into()),
                };
                let range = resolve_sort(&engine, &sorts, &od.range)?;
                engine.register_smt_number(sym, range, kind);
            }
            _ => {}
        }
    }

    // Attach constructor, strategy, and built-in attributes after every symbol profile exists. Polymorphic
    // instances share one resolved attribute set.
    // A symbol can be reached by more than one declaration. Two kinds occur: (a) a later decl *upgrades*
    // an earlier one's special — NAT's `_+_` (no `minus`) and INT's `_+_` (with `minus`) share a symbol
    // (Nat/Int are one kind), and the later (INT) must win; (b) an ad-hoc re-import re-adds an *identical*
    // op — a parameter theory `protecting BOOL` and a regular `BOOL` import both contribute
    // `if_then_else_fi`. So `set_special` is last-wins (handling a), and made idempotent for a re-attached
    // `Branch` (handling b — its "no user strat" assert would otherwise trip on the seam's own strat).
    // The canonical META-LEVEL hook set: `metaReduce` carries the full `op-hook` list; every other descent
    // op declares only `op-hook shareWith (metaReduce …)`. Resolve `metaReduce`'s once (order-independent —
    // by spec shape, not declaration position) so all sharers can clone it (see the `MetaLevelOpSymbol` arm).
    let canonical_meta =
        find_canonical_meta_hooks(pm, &sym_by_profile, &sorts, engine.sorts(), interner);

    // `ditto` inherits from the preceding source declaration in the same overload family. A family is
    // identified before kernel folding (canonical name + arity): disconnected kinds therefore still see
    // the attachment they inherit, while a declaration with no source to inherit from is rejected instead
    // of silently becoming an ordinary operator.
    let mut attr_source_by_group: HashMap<(String, usize), usize> = HashMap::new();
    let mut attr_sources = Vec::with_capacity(pm.ops.len());
    for (idx, od) in pm.ops.iter().enumerate() {
        let name = canonical_name(&od.name, interner);
        let group = (name.clone(), od.domain.len());
        let source = if od.attrs.ditto {
            attr_source_by_group.get(&group).copied().ok_or_else(|| {
                format!(
                    "operator `{name}` uses `ditto` without a preceding declaration of the same arity"
                )
            })?
        } else {
            idx
        };
        attr_source_by_group.insert(group, source);
        attr_sources.push(source);
    }

    let mut pending_host_bindings: Vec<PendingHostBinding> = Vec::new();
    let mut host_binding_index = HashMap::new();
    let mut host_key_by_group: HashMap<(String, usize), String> = HashMap::new();
    let mut unattached_host_groups = HashSet::new();
    for (idx, od) in pm.ops.iter().enumerate() {
        let attrs = &pm.ops[attr_sources[idx]].attrs;
        let name = canonical_name(&od.name, interner);
        let arity = od.domain.len();
        let host_group = (name.clone(), arity);
        let host_attachment = match attrs
            .special
            .as_ref()
            .and_then(|spec| spec.id_hook.as_ref().map(|hook| (spec, hook)))
        {
            Some((spec, (class, data))) if class == "HostFunctionSymbol" => {
                if data.len() != 1 {
                    return Err(format!(
                        "strict host operator `{}` requires exactly one HostFunctionSymbol \
                         capability key",
                        name
                    ));
                }
                if attrs.poly.is_some() || op_syms[idx].len() != 1 {
                    return Err(format!(
                        "strict host operator `{}` cannot use a polymorphic declaration",
                        name
                    ));
                }
                let profile = decl_profiles[idx]
                    .first()
                    .ok_or_else(|| "missing strict host operator profile".to_string())?;
                if let Some(raw) = &attrs.strat
                    && !strict_eager_source_strategy(raw, arity)
                {
                    return Err(format!(
                        "strict host operator `{}` must use argument order 1 through {arity} \
                         followed by at most one final top attempt",
                        name
                    ));
                }
                let hooks = resolve_host_attachment(
                    spec,
                    &data[0],
                    profile,
                    host_functions,
                    &sym_by_profile,
                    &sorts,
                    engine.sorts(),
                    interner,
                )
                .map_err(|error| format!("strict host operator `{}`: {error}", name))?;
                Some((data[0].clone(), hooks))
            }
            _ => None,
        };
        match &host_attachment {
            Some((key, _)) => {
                if unattached_host_groups.contains(&host_group) {
                    return Err(format!(
                        "strict host operator `{name}` is merged with a declaration that has no matching \
                         HostFunctionSymbol attachment"
                    ));
                }
                match host_key_by_group.get(&host_group) {
                    Some(previous) if previous != key => {
                        return Err(format!(
                            "strict host operator `{name}` has inconsistent overload bindings"
                        ));
                    }
                    Some(_) => {}
                    None => {
                        host_key_by_group.insert(host_group.clone(), key.clone());
                    }
                }
            }
            None => {
                if host_key_by_group.contains_key(&host_group) {
                    return Err(format!(
                        "strict host operator `{name}` is merged with a declaration that has no matching \
                         HostFunctionSymbol attachment"
                    ));
                }
                unattached_host_groups.insert(host_group);
            }
        }
        let mut special = match &attrs.special {
            Some(spec) => special_op(
                spec,
                arity,
                &name_to_sym,
                &succ_zero,
                &sym_by_profile,
                &sorts,
                engine.sorts(),
                &canonical_meta,
                interner,
            )?,
            None => None,
        };
        // Polymorphic expansion creates one `_.=._` instance per kind in kind order, making
        // `op_syms[idx]` the sibling table used by decomposition.
        if let Some(SpecialOp::DecomposeEquality { siblings, .. }) = &mut special {
            let n = engine.sorts().num_kinds();
            *siblings = (0..n).map(|k| op_syms[idx].get(k).copied()).collect();
        }
        // META-TERM's `<Qids> : -> Sort/Kind/Constant/Variable` declarations record the quoted-identifier
        // classification sorts, so a `Qid` constant's least sort becomes text-dependent (a `'NzNat` is a
        // `Sort`, `'0.Zero` a `Constant`, …) — needed for the meta-representation to be well-sorted.
        if let Some(spec) = &attrs.special
            && let Some((class, data)) = &spec.id_hook
            && class == "QuotedIdentifierSymbol"
        {
            let range = resolve_sort(&engine, &sorts, &od.range)?;
            engine.set_qid_class(data.first().map(String::as_str), range);
        }
        // Marker-only built-ins must remain distinguishable from ordinary symbols for `.=.` stability:
        // built-in successors stay unreduced, while user-defined iteration operators may decompose.
        let marker = matches!(
            attrs.special.as_ref().and_then(|s| s.id_hook.as_ref()),
            Some((class, _))
                if matches!(
                    class.as_str(),
                    "SuccSymbol" | "StringSymbol" | "FloatSymbol" | "QuotedIdentifierSymbol"
                        | "SystemTrue" | "SystemFalse" | "ObjectConstructorSymbol"
                )
        );
        for &sym in &op_syms[idx] {
            if marker {
                engine.set_symbol_class(sym, tnk_core::symbol::SymbolClass::Marker);
            }
            if let Some(strat) = &attrs.strat {
                engine.set_strategy(sym, strat);
            }
            if let Some(frozen) = &attrs.frozen {
                // An invalid `frozen` attribute is ignored atomically; diagnostics are emitted at the
                // frontend/session boundary.
                let _ = engine.set_frozen(sym, frozen);
            }
            // Store CONFIG/OBJECT/MESSAGE/PORTAL roles on the kernel symbol. They are metadata for
            // ordinary rewriting and drive object/message partitioning in `erewrite`.
            if attrs.config || attrs.object || attrs.message || attrs.portal {
                engine.set_oo_flags(sym, attrs.config, attrs.object, attrs.message, attrs.portal);
            }
            if let Some(op) = &special {
                engine.set_special(sym, op.clone());
                if let SpecialOp::Smt { op } = op {
                    engine.register_smt_operator(sym, *op);
                }
            }
            if let Some((key, hooks)) = &host_attachment {
                engine
                    .validate_host_function_binding(sym, key, hooks)
                    .map_err(|error| format!("strict host operator `{}`: {error}", name))?;
                match host_binding_index.get(&sym).copied() {
                    Some(binding_index) => {
                        let previous: &PendingHostBinding = &pending_host_bindings[binding_index];
                        if previous.key != *key || previous.hooks != *hooks {
                            return Err(format!(
                                "strict host operator `{}` has inconsistent overload bindings",
                                canonical_name(&od.name, interner)
                            ));
                        }
                    }
                    None => {
                        host_binding_index.insert(sym, pending_host_bindings.len());
                        pending_host_bindings.push(PendingHostBinding {
                            symbol: sym,
                            key: key.clone(),
                            hooks: hooks.clone(),
                        });
                    }
                }
            }
        }
    }

    // Overload flags record whether another symbol shares the name, domain-kind profile, or range
    // kind. Symbols with the same name in one connected component share a declaration group, so these
    // flags describe only cross-kind overloading used by print disambiguation.
    let overload = compute_overload_flags(&engine, &syntax);

    // Resolve declared variables `(name, sort)` for the grammar builder + `build_term`.
    let mut vars: Vec<(String, SortId)> = Vec::new();
    for vd in &pm.vars {
        let sort = resolve_sort(&engine, &sorts, &vd.sort)?;
        for name in &vd.names {
            vars.push((name.clone(), sort));
        }
    }

    let integer_literal_kind_count = engine.integer_literal_kind_count();
    let overloaded_naturals = ops
        .keys()
        .filter_map(|(name, arity)| {
            if *arity != 0 || name.is_empty() || !name.bytes().all(|b| b.is_ascii_digit()) {
                return None;
            }
            let canonical = name.trim_start_matches('0');
            (!canonical.is_empty()).then(|| canonical.to_string())
        })
        .collect();

    // A nullary operator spelled as one literal token (TNK-LEX-003) that a literal production of this
    // module also accepts has two parses. Each family follows its grammar terminal: a numeral needs a
    // nonzero digit because the successor production accepts only positive values (`0` parses as the
    // zero constant alone), and a glued rational needs both division and unary minus. String,
    // quoted-identifier, and float values are decoded as the term builder decodes the literal token, so
    // the printer can also qualify the literal that collides. SMT number kinds are not tracked here.
    let mut literal_named_constants = HashSet::new();
    let mut overloaded_strings = HashSet::new();
    let mut overloaded_qids = HashSet::new();
    let mut overloaded_floats = HashSet::new();
    for (&sym, syn) in &syntax {
        if !syn.domain.is_empty() {
            continue;
        }
        let name = engine.symbol(sym).name();
        let literal_spelled = match crate::lex::classify(name) {
            TokKind::Str if string_sym.is_some() => {
                overloaded_strings.insert(crate::build_term::unquote_string(name));
                true
            }
            TokKind::Qid if qid_sym.is_some() => {
                overloaded_qids.insert(name.strip_prefix('\'').unwrap_or(name).to_string());
                true
            }
            TokKind::Float if float_sym.is_some() => {
                if let Ok(value) = name.parse::<f64>() {
                    overloaded_floats.insert(value.to_bits());
                }
                true
            }
            TokKind::Number => nat_succ.is_some() && name.bytes().any(|b| b != b'0'),
            TokKind::NegNumber => minus_sym.is_some(),
            TokKind::Rational => division_sym.is_some() && minus_sym.is_some(),
            _ => false,
        };
        if literal_spelled {
            literal_named_constants.insert(sym);
        }
    }

    Ok(BuiltModule {
        engine,
        name: pm.name.clone(),
        sorts,
        ops,
        syntax,
        op_profiles,
        vars,
        statements: Vec::new(), // loaded separately after the module grammar is available
        eq_traces: Vec::new(),  // populated with source-form trace metadata by load_statements
        pending_host_bindings,
        mb_traces: Vec::new(),
        rl_traces: Vec::new(),
        oo_completion_diagnostics: Vec::new(),
        nat_succ,
        nat_zero,
        string_sym,
        float_sym,
        qid_sym,
        minus_sym,
        division_sym,
        true_sym,
        false_sym,
        overload,
        integer_literal_kind_count,
        overloaded_naturals,
        literal_named_constants,
        overloaded_strings,
        overloaded_qids,
        overloaded_floats,
        strat_decls: pm.strat_decls.clone(),
        strat_defs: pm.strat_defs.clone(),
        identity_specs,
    })
}

/// Compute the per-symbol ad-hoc overloading flags ([`BuiltModule::overload`]) by comparing every pair of
/// symbols that share a (canonical) name: same name ⇒ `ADHOC`; same name and per-position domain kinds ⇒
/// `DOMAIN`; same name and range kind ⇒ `RANGE`; same name and both `iter` ⇒ `ITER`. Only symbols that
/// pick up at least one flag are recorded.
fn compute_overload_flags(
    engine: &Engine,
    syntax: &HashMap<SymbolId, SymbolSyntax>,
) -> HashMap<SymbolId, u8> {
    use crate::sig::syntax::{OVL_ADHOC, OVL_DOMAIN, OVL_ITER, OVL_RANGE};
    // Group symbols by `(name, arity)`, recording domain and range kinds and the effective `iter` flag.
    // Only declarations with the same arity can compete for an application, so a different-arity
    // overload does not force range disambiguation; for example, the four-argument
    // `metaParse(M, none, Q, T)` can keep `none` bare.
    type Profile = (SymbolId, Vec<KindId>, KindId, bool);
    let mut by_name: HashMap<(&str, usize), Vec<Profile>> = HashMap::new();
    for (&sym, syn) in syntax {
        let dom: Vec<KindId> = syn
            .domain
            .iter()
            .map(|&s| engine.sorts().kind_of(s))
            .collect();
        let range = engine.sorts().kind_of(syn.range);
        by_name
            .entry((engine.symbol(sym).name(), dom.len()))
            .or_default()
            .push((sym, dom, range, syn.iter));
    }
    let mut flags: HashMap<SymbolId, u8> = HashMap::new();
    for group in by_name.values() {
        if group.len() < 2 {
            continue; // a unique name needs no disambiguation
        }
        for (sym, dom, range, iter) in group {
            let mut f = OVL_ADHOC; // some other symbol in the group shares the name
            for (other, odom, orange, oiter) in group {
                if other == sym {
                    continue;
                }
                if odom == dom {
                    f |= OVL_DOMAIN;
                }
                if orange == range {
                    f |= OVL_RANGE;
                }
                if *iter && *oiter {
                    f |= OVL_ITER;
                }
            }
            flags.insert(*sym, f);
        }
    }
    flags
}

/// Declare one operator via the kernel constructor for its theory. Identity slots are attached by the
/// caller after every declaration exists; constructors therefore receive no provisional constant.
fn declare_op(
    engine: &mut Engine,
    name: &str,
    attrs: &Attrs,
    effective: EffectiveAxioms,
    domain: &[SortId],
    range: SortId,
) -> SymbolId {
    let symbol = if effective.iter {
        engine.add_op_iter(name.to_string(), domain.to_vec(), range)
    } else if effective.assoc && effective.comm {
        engine.add_op_ac(name.to_string(), domain.to_vec(), range, None)
    } else if effective.assoc {
        engine.add_op_au(name.to_string(), domain.to_vec(), range, None)
    } else if effective.comm || effective.idem || effective.identity {
        engine.add_op_cui(
            name.to_string(),
            domain.to_vec(),
            range,
            effective.comm,
            effective.idem,
            None,
        )
    } else {
        engine.add_op(name.to_string(), domain.to_vec(), range)
    };
    if attrs.ctor {
        engine.set_ctor(symbol);
    }
    symbol
}

// ---- hook resolution ----

fn op_hook_sym(
    spec: &SpecialSpec,
    purpose: &str,
    name_to_sym: &HashMap<String, SymbolId>,
    i: &Interner,
) -> Option<SymbolId> {
    let (_, sig) = spec.op_hooks.iter().find(|(p, _)| p == purpose)?;
    // Use operator-declaration canonicalization. A backquoted blank in a hook signature
    // (`op_to`term_.`) produces adjacent identifier tokens whose boundary must remain in the symbol key.
    let colon = sig.iter().position(|t| i.resolve(t.sym) == ":")?;
    let name = canonical_name(&sig[..colon], i);
    name_to_sym.get(&name).copied()
}

fn term_hook_sym(
    spec: &SpecialSpec,
    purpose: &str,
    name_to_sym: &HashMap<String, SymbolId>,
    i: &Interner,
) -> Option<SymbolId> {
    let (_, term) = spec.term_hooks.iter().find(|(p, _)| p == purpose)?;
    name_to_sym.get(i.resolve(term.first()?.sym)).copied()
}
#[allow(clippy::too_many_arguments)]
fn resolve_host_attachment(
    spec: &SpecialSpec,
    key_text: &str,
    host_profile: &OpProfile,
    host_functions: &HostFunctionCatalog,
    sym_by_profile: &HashMap<(String, Vec<KindId>, KindId), SymbolId>,
    sorts: &HashMap<String, SortId>,
    sort_table: &tnk_core::sort::Sorts,
    interner: &Interner,
) -> R<ResolvedHostHooks> {
    let key = HostFunctionKey::parse(key_text)
        .map_err(|error| format!("invalid HostFunctionSymbol key `{key_text}`: {error}"))?;
    let descriptor = host_functions
        .descriptor_for(&key)
        .ok_or_else(|| format!("missing host capability `{key}`"))?;
    if host_profile.domain.len() != descriptor.arity() {
        return Err(format!(
            "HostFunctionSymbol `{key}` requires arity {}, found {}",
            descriptor.arity(),
            host_profile.domain.len()
        ));
    }
    validate_host_hook_purposes(spec, descriptor, &key)?;

    let mut hooks = ResolvedHostHooks::builder();
    for requirement in descriptor.required_op_hooks() {
        let (_, signature) = spec
            .op_hooks
            .iter()
            .find(|(purpose, _)| purpose == requirement.purpose())
            .ok_or_else(|| {
                format!(
                    "HostFunctionSymbol `{key}` missing op-hook `{}`",
                    requirement.purpose()
                )
            })?;
        let symbol = resolve_op_hook_sig(signature, sym_by_profile, sorts, sort_table, interner)
            .ok_or_else(|| {
                format!(
                    "HostFunctionSymbol `{key}` cannot resolve op-hook `{}`",
                    requirement.purpose()
                )
            })?;
        hooks = hooks.op(requirement.purpose(), symbol);
    }
    for requirement in descriptor.required_term_hooks() {
        let (_, term) = spec
            .term_hooks
            .iter()
            .find(|(purpose, _)| purpose == requirement.purpose())
            .ok_or_else(|| {
                format!(
                    "HostFunctionSymbol `{key}` missing term-hook `{}`",
                    requirement.purpose()
                )
            })?;
        let expected_sort = match requirement.sort() {
            HookSort::Argument(position) => host_profile.domain[position],
            HookSort::Result => host_profile.range,
        };
        let expected_kind = sort_table.kind_of(expected_sort);
        let term = strip_outer_parens(term, interner);
        if term.is_empty() {
            return Err(format!(
                "HostFunctionSymbol `{key}` term-hook `{}` is empty",
                requirement.purpose()
            ));
        }
        let name = canonical_name(term, interner);
        let symbol = sym_by_profile
            .get(&(name, Vec::new(), expected_kind))
            .copied()
            .ok_or_else(|| {
                format!(
                    "HostFunctionSymbol `{key}` term-hook `{}` must resolve to a constant in the expected kind",
                    requirement.purpose()
                )
            })?;
        hooks = hooks.constant_term(requirement.purpose(), symbol);
    }
    hooks.build().map_err(|error| error.to_string())
}

fn validate_host_hook_purposes(
    spec: &SpecialSpec,
    descriptor: &StrictReducerDescriptor,
    key: &HostFunctionKey,
) -> R<()> {
    let required_ops: HashSet<&str> = descriptor
        .required_op_hooks()
        .iter()
        .map(|requirement| requirement.purpose())
        .collect();
    let required_terms: HashSet<&str> = descriptor
        .required_term_hooks()
        .iter()
        .map(|requirement| requirement.purpose())
        .collect();
    let mut seen = HashSet::new();
    for (purpose, _) in &spec.op_hooks {
        if !seen.insert(purpose.as_str()) {
            return Err(format!(
                "HostFunctionSymbol `{key}` repeats hook purpose `{purpose}`"
            ));
        }
        if !required_ops.contains(purpose.as_str()) {
            return Err(format!(
                "HostFunctionSymbol `{key}` has unexpected op-hook `{purpose}`"
            ));
        }
    }
    for (purpose, _) in &spec.term_hooks {
        if !seen.insert(purpose.as_str()) {
            return Err(format!(
                "HostFunctionSymbol `{key}` repeats hook purpose `{purpose}`"
            ));
        }
        if !required_terms.contains(purpose.as_str()) {
            return Err(format!(
                "HostFunctionSymbol `{key}` has unexpected term-hook `{purpose}`"
            ));
        }
    }
    Ok(())
}

fn nat_hooks(
    spec: &SpecialSpec,
    name_to_sym: &HashMap<String, SymbolId>,
    succ_zero: &HashMap<SymbolId, SymbolId>,
    i: &Interner,
) -> R<NatHooks> {
    let succ =
        op_hook_sym(spec, "succSymbol", name_to_sym, i).ok_or("missing op-hook succSymbol")?;
    let zero = succ_zero
        .get(&succ)
        .copied()
        .ok_or("succSymbol has no recorded zeroTerm")?;
    let minus = op_hook_sym(spec, "minusSymbol", name_to_sym, i);
    Ok(NatHooks { succ, zero, minus })
}

fn bool_hooks(
    spec: &SpecialSpec,
    name_to_sym: &HashMap<String, SymbolId>,
    i: &Interner,
) -> Option<BoolHooks> {
    Some(BoolHooks {
        true_: term_hook_sym(spec, "trueTerm", name_to_sym, i)?,
        false_: term_hook_sym(spec, "falseTerm", name_to_sym, i)?,
    })
}

/// Map a `special` directive to a kernel [`SpecialOp`] (or `None` for the pure NA-constant / successor
/// markers, which carry no reduction rule — their behaviour is the theory / the literal productions).
#[allow(clippy::too_many_arguments)]
fn special_op(
    spec: &SpecialSpec,
    arity: usize,
    name_to_sym: &HashMap<String, SymbolId>,
    succ_zero: &HashMap<SymbolId, SymbolId>,
    sym_by_profile: &HashMap<(String, Vec<KindId>, KindId), SymbolId>,
    sorts: &HashMap<String, SortId>,
    sort_table: &tnk_core::sort::Sorts,
    canonical_meta: &Option<std::rc::Rc<MetaHooks>>,
    i: &Interner,
) -> R<Option<SpecialOp>> {
    let Some((class, data)) = &spec.id_hook else {
        return Ok(None);
    };
    let code = data.first().map(String::as_str);
    let op = match class.as_str() {
        // Marker hooks do not reduce. Literal anchors remain registered for condition and hook lookup.
        "SuccSymbol"
        | "StringSymbol"
        | "FloatSymbol"
        | "QuotedIdentifierSymbol"
        | "SystemTrue"
        | "SystemFalse"
        | "SMT_NumberSymbol" => return Ok(None),
        // CONFIGURATION's object constructor is an ordinary free symbol for reduction and rewriting.
        // Its AttributeSet hook informs object-pattern completion; object/message scheduling uses the
        // role flags attached above.
        "ObjectConstructorSymbol" => return Ok(None),
        "MinusSymbol" => SpecialOp::Minus {
            nat: nat_hooks(spec, name_to_sym, succ_zero, i)?,
        },
        "DivisionSymbol" => SpecialOp::Division {
            nat: nat_hooks(spec, name_to_sym, succ_zero, i)?,
        },
        "SMT_Symbol" => SpecialOp::Smt {
            op: smt_op(code.ok_or("SMT_Symbol code")?, arity)?,
        },
        // `_==_`/`_=/=_` compare the two reduced arguments structurally, including nonground arguments;
        // distinct variables compare unequal.
        "EqualitySymbol" => SpecialOp::Equality {
            eq: term_hook_sym(spec, "equalTerm", name_to_sym, i).ok_or("equalTerm")?,
            neq: term_hook_sym(spec, "notEqualTerm", name_to_sym, i).ok_or("notEqualTerm")?,
        },
        // The initial-equality predicate `_.=._`: decides ground/provably-unequal cases and
        // *decomposes* symbolic ones over stable constructors into `_and_`/`_or_` of smaller
        // problems. The per-kind sibling-instance table is attached after polymorphic expansion.
        "CommutativeDecomposeEqualitySymbol" => SpecialOp::DecomposeEquality {
            eq: term_hook_sym(spec, "equalTerm", name_to_sym, i).ok_or("equalTerm")?,
            neq: term_hook_sym(spec, "notEqualTerm", name_to_sym, i).ok_or("notEqualTerm")?,
            conj: op_hook_sym(spec, "conjunctionSymbol", name_to_sym, i),
            disj: op_hook_sym(spec, "disjunctionSymbol", name_to_sym, i),
            siblings: std::rc::Rc::from(Vec::new()),
        },
        "BranchSymbol" => {
            // term-hooks "1", "2", … are the test constants, in order.
            let mut tests = Vec::new();
            for k in 1.. {
                match term_hook_sym(spec, &k.to_string(), name_to_sym, i) {
                    Some(s) => tests.push(s),
                    None => break,
                }
            }
            SpecialOp::Branch { tests }
        }
        "ACU_NumberOpSymbol" => SpecialOp::AcuNumberOp {
            op: num_op(code.ok_or("ACU_NumberOpSymbol code")?)?,
            nat: nat_hooks(spec, name_to_sym, succ_zero, i)?,
        },
        "CUI_NumberOpSymbol" => SpecialOp::CuiNumberOp {
            op: num_op(code.ok_or("CUI_NumberOpSymbol code")?)?,
            nat: nat_hooks(spec, name_to_sym, succ_zero, i)?,
        },
        "NumberOpSymbol" => SpecialOp::NumberOp {
            op: num_op(code.ok_or("NumberOpSymbol code")?)?,
            nat: nat_hooks(spec, name_to_sym, succ_zero, i)?,
            bool_: bool_hooks(spec, name_to_sym, i),
        },
        "StringOpSymbol" => match conv_op("StringOpSymbol", code.unwrap_or(""), arity) {
            Some(op) => conversion(op, spec, name_to_sym, succ_zero, i),
            None => SpecialOp::StringOp {
                op: str_op(code.ok_or("StringOpSymbol code")?)?,
                str_sym: op_hook_sym(spec, "stringSymbol", name_to_sym, i)
                    .ok_or("StringOpSymbol stringSymbol")?,
                nat: nat_hooks(spec, name_to_sym, succ_zero, i).ok(),
                bool_: bool_hooks(spec, name_to_sym, i),
                not_found: term_hook_sym(spec, "notFoundTerm", name_to_sym, i),
            },
        },
        "RandomOpSymbol" => SpecialOp::Random {
            nat: nat_hooks(spec, name_to_sym, succ_zero, i)?,
        },
        "CounterSymbol" => SpecialOp::Counter {
            nat: nat_hooks(spec, name_to_sym, succ_zero, i)?,
        },
        "QuotedIdentifierOpSymbol" => match code.ok_or("QuotedIdentifierOpSymbol code")? {
            // LEXICAL needs the frontend's byte-aware token scanner, so these two quoted-identifier
            // operations use the same upper-layer descent seam as META-LEVEL rather than becoming inert
            // or teaching the kernel about source tokens.
            "tokenize" => SpecialOp::Meta {
                op: MetaOp::Tokenize,
                hooks: std::rc::Rc::new(resolve_meta_hooks(
                    spec,
                    sym_by_profile,
                    sorts,
                    sort_table,
                    i,
                )),
            },
            "printTokens" => SpecialOp::Meta {
                op: MetaOp::PrintTokens,
                hooks: std::rc::Rc::new(resolve_meta_hooks(
                    spec,
                    sym_by_profile,
                    sorts,
                    sort_table,
                    i,
                )),
            },
            code => SpecialOp::QidOp {
                op: match qid_op(code) {
                    Ok(op) => op,
                    Err(_) => return Ok(None),
                },
                qid_sym: op_hook_sym(spec, "quotedIdentifierSymbol", name_to_sym, i)
                    .ok_or("QuotedIdentifierOpSymbol quotedIdentifierSymbol")?,
                str_sym: op_hook_sym(spec, "stringSymbol", name_to_sym, i)
                    .ok_or("QuotedIdentifierOpSymbol stringSymbol")?,
            },
        },
        "FloatOpSymbol" => match conv_op("FloatOpSymbol", code.unwrap_or(""), arity) {
            Some(op) => conversion(op, spec, name_to_sym, succ_zero, i),
            None => SpecialOp::FloatOp {
                op: flt_op(code.ok_or("FloatOpSymbol code")?, arity)?,
                float_sym: op_hook_sym(spec, "floatSymbol", name_to_sym, i)
                    .ok_or("FloatOpSymbol floatSymbol")?,
                bool_: bool_hooks(spec, name_to_sym, i),
            },
        },
        // META-LEVEL descent functions share metaReduce's representation hooks. A standalone
        // extension may add operation-specific structural hooks; merge those over the canonical
        // table instead of discarding them merely because META-LEVEL is imported.
        "MetaLevelOpSymbol" => {
            let code = code.ok_or("MetaLevelOpSymbol code")?;
            let mut hooks = canonical_meta.as_deref().cloned().unwrap_or_default();
            let own = resolve_meta_hooks(spec, sym_by_profile, sorts, sort_table, i);
            hooks.ops.extend(own.ops);
            hooks.terms.extend(own.terms);
            SpecialOp::Meta {
                op: meta_op(code),
                hooks: std::rc::Rc::new(hooks),
            }
        }
        "ModelCheckerSymbol" => {
            let op_hook = |purpose: &str| -> R<SymbolId> {
                let (_, signature) = spec
                    .op_hooks
                    .iter()
                    .find(|(candidate, _)| candidate == purpose)
                    .ok_or_else(|| format!("ModelCheckerSymbol missing op-hook {purpose}"))?;
                resolve_op_hook_sig(signature, sym_by_profile, sorts, sort_table, i)
                    .ok_or_else(|| format!("ModelCheckerSymbol cannot resolve op-hook {purpose}"))
            };
            SpecialOp::ModelCheck {
                hooks: std::rc::Rc::new(ModelCheckerHooks {
                    temporal: TemporalHooks {
                        true_symbol: op_hook("trueSymbol")?,
                        false_symbol: op_hook("falseSymbol")?,
                        not_symbol: op_hook("notSymbol")?,
                        next_symbol: op_hook("nextSymbol")?,
                        and_symbol: op_hook("andSymbol")?,
                        or_symbol: op_hook("orSymbol")?,
                        until_symbol: op_hook("untilSymbol")?,
                        release_symbol: op_hook("releaseSymbol")?,
                    },
                    satisfies_symbol: op_hook("satisfiesSymbol")?,
                    qid_symbol: op_hook("qidSymbol")?,
                    unlabeled_symbol: op_hook("unlabeledSymbol")?,
                    deadlock_symbol: op_hook("deadlockSymbol")?,
                    transition_symbol: op_hook("transitionSymbol")?,
                    transition_list_symbol: op_hook("transitionListSymbol")?,
                    nil_transition_list_symbol: op_hook("nilTransitionListSymbol")?,
                    counterexample_symbol: op_hook("counterexampleSymbol")?,
                    true_term: term_hook_sym(spec, "trueTerm", name_to_sym, i)
                        .ok_or("ModelCheckerSymbol cannot resolve term-hook trueTerm")?,
                }),
            }
        }
        "SatSolverSymbol" => {
            let op_hook = |purpose: &str| -> R<SymbolId> {
                let (_, signature) = spec
                    .op_hooks
                    .iter()
                    .find(|(candidate, _)| candidate == purpose)
                    .ok_or_else(|| format!("SatSolverSymbol missing op-hook {purpose}"))?;
                resolve_op_hook_sig(signature, sym_by_profile, sorts, sort_table, i)
                    .ok_or_else(|| format!("SatSolverSymbol cannot resolve op-hook {purpose}"))
            };
            SpecialOp::SatSolve {
                hooks: std::rc::Rc::new(SatSolverHooks {
                    temporal: TemporalHooks {
                        true_symbol: op_hook("trueSymbol")?,
                        false_symbol: op_hook("falseSymbol")?,
                        not_symbol: op_hook("notSymbol")?,
                        next_symbol: op_hook("nextSymbol")?,
                        and_symbol: op_hook("andSymbol")?,
                        or_symbol: op_hook("orSymbol")?,
                        until_symbol: op_hook("untilSymbol")?,
                        release_symbol: op_hook("releaseSymbol")?,
                    },
                    formula_list_symbol: op_hook("formulaListSymbol")?,
                    nil_formula_list_symbol: op_hook("nilFormulaListSymbol")?,
                    model_symbol: op_hook("modelSymbol")?,
                    false_term: term_hook_sym(spec, "falseTerm", name_to_sym, i)
                        .ok_or("SatSolverSymbol cannot resolve term-hook falseTerm")?,
                }),
            }
        }
        // META-INTERPRETER's local synchronous external-object manager. Protocol decoding belongs to
        // tnk-session; the kernel binding only makes the no-local-object scheduler branch offer messages
        // to the host-owned ExternalManager seam.
        "InterpreterManagerSymbol" => SpecialOp::InterpreterManager,
        // `stdin`/`stdout`/`stderr`: standard-stream external-object managers. The id-hook selects the
        // stream, and op-hooks identify the write/reply and line-input message symbols.
        "StreamManagerSymbol" => SpecialOp::StreamManager {
            stream: match code {
                Some("stdin") => StdStream::Stdin,
                Some("stdout") => StdStream::Stdout,
                Some("stderr") => StdStream::Stderr,
                _ => return Err("StreamManagerSymbol needs a stdin/stdout/stderr id-hook".into()),
            },
            string_sym: op_hook_sym(spec, "stringSymbol", name_to_sym, i),
            write_msg: op_hook_sym(spec, "writeMsg", name_to_sym, i),
            wrote_msg: op_hook_sym(spec, "wroteMsg", name_to_sym, i),
            get_line_msg: op_hook_sym(spec, "getLineMsg", name_to_sym, i),
            got_line_msg: op_hook_sym(spec, "gotLineMsg", name_to_sym, i),
        },
        // Unsupported id-hook classes (MatrixOpSymbol, LoopSymbol, ...) are declared without a special
        // binding. Their operators remain inert while the rest of the module remains executable.
        _other => return Ok(None),
    };
    Ok(Some(op))
}

/// Map an `SMT_Symbol` attachment code and arity to the typed operation. Arity disambiguates `-`.
fn smt_op(code: &str, arity: usize) -> R<SmtOp> {
    Ok(match (code, arity) {
        ("true", 0) => SmtOp::True,
        ("false", 0) => SmtOp::False,
        ("not", 1) => SmtOp::Not,
        ("and", 2) => SmtOp::And,
        ("or", 2) => SmtOp::Or,
        ("xor", 2) => SmtOp::Xor,
        ("implies", 2) => SmtOp::Implies,
        ("===", 2) => SmtOp::Equals,
        ("=/==", 2) => SmtOp::NotEquals,
        ("ite", 3) => SmtOp::Ite,
        ("-", 1) => SmtOp::UnaryMinus,
        ("-", 2) => SmtOp::Minus,
        ("+", 2) => SmtOp::Plus,
        ("*", 2) => SmtOp::Multiply,
        ("div", 2) => SmtOp::Divide,
        ("mod", 2) => SmtOp::Modulo,
        ("<", 2) => SmtOp::Less,
        ("<=", 2) => SmtOp::LessEqual,
        (">", 2) => SmtOp::Greater,
        (">=", 2) => SmtOp::GreaterEqual,
        ("divisible", 2) => SmtOp::Divisible,
        ("/", 2) => SmtOp::RealDivide,
        ("toReal", 1) => SmtOp::ToReal,
        ("toInteger", 1) => SmtOp::ToInteger,
        ("isInteger", 1) => SmtOp::IsInteger,
        _ => return Err(format!("unsupported SMT operator `{code}`/{arity}")),
    })
}

/// Map a `MetaLevelOpSymbol` code to its upper-layer operation.
fn meta_op(code: &str) -> MetaOp {
    match code {
        "metaReduce" => MetaOp::Reduce,
        "metaNormalize" => MetaOp::Normalize,
        "metaRewrite" => MetaOp::Rewrite,
        "metaFrewrite" => MetaOp::Frewrite,
        "metaApply" => MetaOp::Apply,
        "metaXapply" => MetaOp::Xapply,
        "metaMatch" => MetaOp::Match,
        "metaXmatch" => MetaOp::Xmatch,
        "metaSearch" => MetaOp::Search,
        "metaSearchPath" => MetaOp::SearchPath,
        "metaCheck" => MetaOp::Check,
        "metaSmtSearch" => MetaOp::SmtSearch,
        "variantSat" => MetaOp::VariantSat {
            validity: false,
            explicit_sorts: false,
        },
        "variantSatWithSorts" => MetaOp::VariantSat {
            validity: false,
            explicit_sorts: true,
        },
        "variantValid" => MetaOp::VariantSat {
            validity: true,
            explicit_sorts: false,
        },
        "variantValidWithSorts" => MetaOp::VariantSat {
            validity: true,
            explicit_sorts: true,
        },
        "variantSatWellFormed" => MetaOp::VariantSatWellFormed,
        "metaSortLeq" => MetaOp::SortLeq,
        "metaSameKind" => MetaOp::SameKind,
        "metaLesserSorts" => MetaOp::LesserSorts,
        "metaGlbSorts" => MetaOp::GlbSorts,
        "metaLeastSort" => MetaOp::LeastSort,
        "metaCompleteName" => MetaOp::CompleteName,
        "metaGetKind" => MetaOp::GetKind,
        "metaGetKinds" => MetaOp::GetKinds,
        "metaMaximalSorts" => MetaOp::MaximalSorts,
        "metaMinimalSorts" => MetaOp::MinimalSorts,
        "metaMaximalAritySet" => MetaOp::MaximalAritySet,
        "metaParse" => MetaOp::Parse,
        "metaPrettyPrint" => MetaOp::PrettyPrint,
        "metaPrintToString" => MetaOp::PrintToString,
        "metaWellFormedModule" => MetaOp::WellFormedModule,
        "metaWellFormedTerm" => MetaOp::WellFormedTerm,
        "metaWellFormedSubstitution" => MetaOp::WellFormedSubstitution,
        "metaUpModule" => MetaOp::UpModule,
        "metaUpImports" => MetaOp::UpImports,
        "metaUpSorts" => MetaOp::UpSorts,
        "metaUpSubsortDecls" => MetaOp::UpSubsortDecls,
        "metaUpOpDecls" => MetaOp::UpOpDecls,
        "metaUpMbs" => MetaOp::UpMbs,
        "metaUpEqs" => MetaOp::UpEqs,
        "metaUpRls" => MetaOp::UpRls,
        "metaUpStratDecls" => MetaOp::UpStratDecls,
        "metaUpSds" => MetaOp::UpSds,
        "metaUpView" => MetaOp::UpView,
        "metaUpTerm" => MetaOp::UpTerm,
        "metaDownTerm" => MetaOp::DownTerm,
        // Both signature families share this dispatch; the third argument selects the result shape.
        "metaUnify" => MetaOp::Unify {
            disjoint: false,
            irredundant: false,
        },
        "metaDisjointUnify" => MetaOp::Unify {
            disjoint: true,
            irredundant: false,
        },
        "metaIrredundantUnify" => MetaOp::Unify {
            disjoint: false,
            irredundant: true,
        },
        "metaIrredundantDisjointUnify" => MetaOp::Unify {
            disjoint: true,
            irredundant: true,
        },
        "legacyMetaUnify" => MetaOp::Unify {
            disjoint: false,
            irredundant: false,
        },
        "legacyMetaDisjointUnify" => MetaOp::Unify {
            disjoint: true,
            irredundant: false,
        },
        // Folding variants support Qid-family and Nat-indexed signatures.
        "metaGetVariant" => MetaOp::GetVariant {
            irredundant: false,
            nat_family: false,
        },
        "metaGetIrredundantVariant" => MetaOp::GetVariant {
            irredundant: true,
            nat_family: false,
        },
        "legacyMetaGetVariant" => MetaOp::GetVariant {
            irredundant: false,
            nat_family: true,
        },
        "legacyMetaGetIrredundantVariant" => MetaOp::GetVariant {
            irredundant: true,
            nat_family: true,
        },
        "metaVariantUnify" => MetaOp::VariantUnify {
            disjoint: false,
            nat_family: false,
        },
        "metaVariantDisjointUnify" => MetaOp::VariantUnify {
            disjoint: true,
            nat_family: false,
        },
        "legacyMetaVariantUnify" => MetaOp::VariantUnify {
            disjoint: false,
            nat_family: true,
        },
        "legacyMetaVariantDisjointUnify" => MetaOp::VariantUnify {
            disjoint: true,
            nat_family: true,
        },
        "metaVariantMatch" => MetaOp::VariantMatch,
        "metaNarrow" => MetaOp::Narrow { state_only: false },
        "metaNarrow2" => MetaOp::Narrow { state_only: true },
        "metaNarrowingApply" => MetaOp::NarrowingApply,
        "metaNarrowingSearch" => MetaOp::NarrowingSearch { path: false },
        "metaNarrowingSearchPath" => MetaOp::NarrowingSearch { path: true },
        // Unknown descent hook ids remain inert.
        _ => MetaOp::Unknown,
    }
}

/// Find and resolve the canonical META-LEVEL hook set: the descent operator with the full `op-hook` list,
/// `metaReduce`. Other descent operators (`metaRewrite`, `metaApply`, and others) declare only
/// `op-hook shareWith (metaReduce …)` and reuse this set, so down/up maps see all representation
/// constructors regardless of declaration order. Returns `None` when the module has no `metaReduce`.
fn find_canonical_meta_hooks(
    pm: &PreModule,
    sym_by_profile: &HashMap<(String, Vec<KindId>, KindId), SymbolId>,
    sorts: &HashMap<String, SortId>,
    sort_table: &tnk_core::sort::Sorts,
    i: &Interner,
) -> Option<std::rc::Rc<MetaHooks>> {
    pm.ops.iter().find_map(|od| {
        let spec = od.attrs.special.as_ref()?;
        let (class, data) = spec.id_hook.as_ref()?;
        if class == "MetaLevelOpSymbol" && data.first().is_some_and(|code| code == "metaReduce") {
            Some(std::rc::Rc::new(resolve_meta_hooks(
                spec,
                sym_by_profile,
                sorts,
                sort_table,
                i,
            )))
        } else {
            None
        }
    })
}

/// Resolve a descent function's `op-hook`/`term-hook` list into the meta-representation symbols the
/// down/up maps need ([`MetaHooks`]), keyed by hook purpose (`qidSymbol`, `metaTermSymbol`, …). Op-hooks
/// resolve by **signature** (name + domain/range kinds), since names like `_,_` / `__` are ad-hoc
/// overloaded across kinds (a TermList `_,_` vs a RenamingSet `_,_`); a hook whose signature names a sort
/// not in this module is skipped (it is simply unavailable to descent).
fn resolve_meta_hooks(
    spec: &SpecialSpec,
    sym_by_profile: &HashMap<(String, Vec<KindId>, KindId), SymbolId>,
    sorts: &HashMap<String, SortId>,
    sort_table: &tnk_core::sort::Sorts,
    i: &Interner,
) -> MetaHooks {
    let mut ops = HashMap::new();
    for (purpose, sig) in &spec.op_hooks {
        if let Some(sym) = resolve_op_hook_sig(sig, sym_by_profile, sorts, sort_table, i) {
            ops.insert(purpose.clone(), sym);
        }
    }
    // The descent functions carry op-hooks only (no term-hooks), so `terms` stays empty.
    MetaHooks {
        ops,
        terms: HashMap::new(),
    }
}

/// Resolve one `op-hook` signature `name : dom… ~> range` to the symbol with that profile (name + the
/// kinds of the domain/range sorts), via [`sym_by_profile`]. Returns `None` if the signature is malformed
/// or names an unknown sort.
fn resolve_op_hook_sig(
    sig: &[crate::lex::Token],
    sym_by_profile: &HashMap<(String, Vec<KindId>, KindId), SymbolId>,
    sorts: &HashMap<String, SortId>,
    sort_table: &tnk_core::sort::Sorts,
    i: &Interner,
) -> Option<SymbolId> {
    let texts: Vec<&str> = sig.iter().map(|t| i.resolve(t.sym)).collect();
    let colon = texts.iter().position(|&t| t == ":")?;
    let arrow = texts.iter().position(|&t| t == "~>" || t == "->")?;
    let name = canonical_name(&sig[..colon], i);
    let domain = resolve_hook_sort_sequence(&sig[colon + 1..arrow], sorts, i)?;
    let dom_kinds = domain
        .into_iter()
        .map(|sort| sort_table.kind_of(sort))
        .collect();
    let range_tokens = sig.get(arrow + 1..)?;
    let range_end = hook_type_end(range_tokens, 0, range_tokens.len(), i)?;
    let range_name = canonical_name(&range_tokens[..range_end], i);
    let range_kind = sort_table.kind_of(*sorts.get(&range_name)?);
    sym_by_profile.get(&(name, dom_kinds, range_kind)).copied()
}

fn hook_type_end(
    tokens: &[crate::lex::Token],
    start: usize,
    limit: usize,
    interner: &Interner,
) -> Option<usize> {
    if start >= limit {
        return None;
    }
    let text = |index: usize| interner.resolve(tokens[index].sym);
    let mut index = start;
    if text(index) == "[" {
        let mut depth = 0i32;
        while index < limit {
            match text(index) {
                "[" => depth += 1,
                "]" => depth -= 1,
                _ => {}
            }
            index += 1;
            if depth == 0 {
                return Some(index);
            }
        }
        return None;
    }

    index += 1;
    while index < limit && text(index) == "{" {
        let mut depth = 0i32;
        while index < limit {
            match text(index) {
                "{" => depth += 1,
                "}" => depth -= 1,
                _ => {}
            }
            index += 1;
            if depth == 0 {
                break;
            }
        }
        if depth != 0 {
            return None;
        }
    }
    Some(index)
}

fn resolve_hook_sort_sequence(
    tokens: &[crate::lex::Token],
    sorts: &HashMap<String, SortId>,
    interner: &Interner,
) -> Option<Vec<SortId>> {
    fn resolve_from(
        start: usize,
        tokens: &[crate::lex::Token],
        sorts: &HashMap<String, SortId>,
        interner: &Interner,
        resolved: &mut Vec<SortId>,
    ) -> bool {
        if start == tokens.len() {
            return true;
        }
        for end in (start + 1..=tokens.len()).rev() {
            let name = canonical_name(&tokens[start..end], interner);
            let Some(&sort) = sorts.get(&name) else {
                continue;
            };
            resolved.push(sort);
            if resolve_from(end, tokens, sorts, interner, resolved) {
                return true;
            }
            resolved.pop();
        }
        false
    }

    let mut resolved = Vec::new();
    resolve_from(0, tokens, sorts, interner, &mut resolved).then_some(resolved)
}

fn num_op(code: &str) -> R<NumOp> {
    Ok(match code {
        "+" => NumOp::Add,
        "*" => NumOp::Mul,
        "gcd" => NumOp::Gcd,
        "lcm" => NumOp::Lcm,
        "min" => NumOp::Min,
        "max" => NumOp::Max,
        "xor" => NumOp::Xor,
        "&" => NumOp::And,
        "|" => NumOp::Or,
        "sd" => NumOp::Sd,
        "-" => NumOp::Sub,
        "quo" => NumOp::Quo,
        "rem" => NumOp::Rem,
        "^" => NumOp::Pow,
        "modExp" => NumOp::ModExp,
        ">>" => NumOp::Shr,
        "<<" => NumOp::Shl,
        "abs" => NumOp::Abs,
        "~" => NumOp::BitNot,
        "<" => NumOp::Lt,
        "<=" => NumOp::Le,
        ">" => NumOp::Gt,
        ">=" => NumOp::Ge,
        "divides" => NumOp::Divides,
        other => return Err(format!("unsupported number op `{other}`")),
    })
}

/// A CONVERSION coercion code, distinguished by id-hook class + code + arity (since `float`/`rat`/
/// `string` are overloaded across argument types — e.g. `string : Rat NzNat` vs `string : Float`).
/// `None` ⇒ not a conversion (an ordinary `FloatOp`/`StringOp` arithmetic/string code).
fn conv_op(class: &str, code: &str, arity: usize) -> Option<ConvOp> {
    Some(match (class, code, arity) {
        ("FloatOpSymbol", "float", 1) => ConvOp::RatToFloat,
        ("FloatOpSymbol", "rat", 1) => ConvOp::FloatToRat,
        ("StringOpSymbol", "string", 2) => ConvOp::RatToString,
        ("StringOpSymbol", "string", 1) => ConvOp::FloatToString,
        ("StringOpSymbol", "rat", 2) => ConvOp::StringToRat,
        ("StringOpSymbol", "float", 1) => ConvOp::StringToFloat,
        ("StringOpSymbol", "decFloat", 2) => ConvOp::DecFloat,
        _ => return None,
    })
}

/// Build a [`SpecialOp::Conversion`], resolving each (optional) hook a conversion might need.
fn conversion(
    op: ConvOp,
    spec: &SpecialSpec,
    name_to_sym: &HashMap<String, SymbolId>,
    succ_zero: &HashMap<SymbolId, SymbolId>,
    i: &Interner,
) -> SpecialOp {
    SpecialOp::Conversion {
        op,
        float_sym: op_hook_sym(spec, "floatSymbol", name_to_sym, i),
        str_sym: op_hook_sym(spec, "stringSymbol", name_to_sym, i),
        nat: nat_hooks(spec, name_to_sym, succ_zero, i).ok(),
        division: op_hook_sym(spec, "divisionSymbol", name_to_sym, i),
        dec_float: op_hook_sym(spec, "decFloatSymbol", name_to_sym, i),
    }
}

fn qid_op(code: &str) -> R<QidOp> {
    Ok(match code {
        "string" => QidOp::String,
        "qid" => QidOp::Qid,
        other => return Err(format!("unsupported quoted-id op `{other}`")),
    })
}

fn str_op(code: &str) -> R<StrOp> {
    Ok(match code {
        "+" => StrOp::Concat,
        "length" => StrOp::Length,
        "substr" => StrOp::Substr,
        "ascii" => StrOp::Ascii,
        "char" => StrOp::Char,
        "find" => StrOp::Find,
        "rfind" => StrOp::Rfind,
        "upperCase" => StrOp::UpperCase,
        "lowerCase" => StrOp::LowerCase,
        "cntrl" => StrOp::IsClass(CharClass::Control),
        "print" => StrOp::IsClass(CharClass::Printable),
        "space" => StrOp::IsClass(CharClass::Space),
        "blank" => StrOp::IsClass(CharClass::Blank),
        "graph" => StrOp::IsClass(CharClass::Graphic),
        "punct" => StrOp::IsClass(CharClass::Punct),
        "alnum" => StrOp::IsClass(CharClass::Alnum),
        "alpha" => StrOp::IsClass(CharClass::Alpha),
        "isupper" => StrOp::IsClass(CharClass::Upper),
        "islower" => StrOp::IsClass(CharClass::Lower),
        "digit" => StrOp::IsClass(CharClass::Digit),
        "xdigit" => StrOp::IsClass(CharClass::XDigit),
        "startsWith" => StrOp::StartsWith,
        "endsWith" => StrOp::EndsWith,
        "ltrim" => StrOp::TrimStart,
        "rtrim" => StrOp::TrimEnd,
        "trim" => StrOp::Trim,
        "<" => StrOp::Lt,
        "<=" => StrOp::Le,
        ">" => StrOp::Gt,
        ">=" => StrOp::Ge,
        other => return Err(format!("unsupported string op `{other}`")),
    })
}

fn flt_op(code: &str, arity: usize) -> R<FltOp> {
    Ok(match (code, arity) {
        ("-", 1) => FltOp::Neg,
        ("abs", _) => FltOp::Abs,
        ("sqrt", _) => FltOp::Sqrt,
        ("floor", _) => FltOp::Floor,
        ("ceiling", _) => FltOp::Ceiling,
        ("exp", _) => FltOp::Exp,
        ("log", _) => FltOp::Log,
        ("sin", _) => FltOp::Sin,
        ("cos", _) => FltOp::Cos,
        ("tan", _) => FltOp::Tan,
        ("asin", _) => FltOp::Asin,
        ("acos", _) => FltOp::Acos,
        ("atan", 1) => FltOp::Atan,
        ("atan", _) => FltOp::Atan2, // binary `atan(y, x)`
        ("+", _) => FltOp::Add,
        ("-", _) => FltOp::Sub,
        ("*", _) => FltOp::Mul,
        ("/", _) => FltOp::Div,
        ("rem", _) => FltOp::Rem,
        ("^", _) => FltOp::Pow,
        ("min", _) => FltOp::Min,
        ("max", _) => FltOp::Max,
        ("<", _) => FltOp::Lt,
        ("<=", _) => FltOp::Le,
        (">", _) => FltOp::Gt,
        (">=", _) => FltOp::Ge,
        (other, _) => return Err(format!("unsupported float op `{other}`")),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lex::tokenize;
    use crate::surface::parser::Parser;
    use tnk_core::variant_sat::{ConstructorAnalysis, EligibilityRejection, SortOverrides};

    fn build(src: &str) -> BuiltModule {
        let mut i = Interner::new();
        let toks = tokenize(src, &mut i);
        let s = Parser::new(&toks, &i).parse_source().expect("parse ok");
        build_module(&s.modules[0], &mut i).expect("build ok")
    }

    /// A source-built signature attaches arithmetic operations and reduces their applications.
    #[test]
    fn nat_signature_reduces_via_special_ops() {
        let src = "\
fmod NATB is
  sorts Truth Zero NzNat Nat .
  subsorts Zero NzNat < Nat .
  ops tt ff : -> Truth [ctor] .
  op 0 : -> Zero [ctor] .
  op s_ : Nat -> NzNat [ctor iter special (id-hook SuccSymbol term-hook zeroTerm (0))] .
  op _+_ : NzNat Nat -> NzNat [assoc comm special (id-hook ACU_NumberOpSymbol (+) op-hook succSymbol (s_ : Nat ~> NzNat))] .
  op _+_ : Nat Nat -> Nat [ditto] .
  op gcd : NzNat Nat -> NzNat [assoc comm special (id-hook ACU_NumberOpSymbol (gcd) op-hook succSymbol (s_ : Nat ~> NzNat))] .
  op gcd : Nat Nat -> Nat [ditto] .
  op _<_ : Nat Nat -> Truth [special (id-hook NumberOpSymbol (<) op-hook succSymbol (s_ : Nat ~> NzNat) term-hook trueTerm (tt) term-hook falseTerm (ff))] .
endfm
";
        let mut m = build(src);
        let (succ, zero) = (m.nat_succ.unwrap(), m.nat_zero.unwrap());
        let num = |m: &mut BuiltModule, n: u64| {
            let z = m.engine.make_const(zero);
            m.engine.make_iter(succ, n, z)
        };
        // 2 + 3 = 5 (ACU_NumberOp), NzNat, 1 rewrite.
        let plus = m.ops[&("_+_".to_string(), 2)];
        let (a, b) = (num(&mut m, 2), num(&mut m, 3));
        let sum = m.engine.make_ac(plus, vec![a, b]);
        m.engine.reset_rewrites();
        let r = m.engine.reduce(sum);
        let five = num(&mut m, 5);
        assert!(m.engine.deep_equal(r, five), "2 + 3 = 5");
        assert_eq!(m.engine.sorts().name(m.engine.sort_of(r)), "NzNat");
        assert_eq!(m.engine.rewrites(), 1);

        // gcd(12, 18) = 6.
        let gcd = m.ops[&("gcd".to_string(), 2)];
        let (a, b) = (num(&mut m, 12), num(&mut m, 18));
        let g = m.engine.make_ac(gcd, vec![a, b]);
        let r = m.engine.reduce(g);
        let six = num(&mut m, 6);
        assert!(m.engine.deep_equal(r, six), "gcd(12, 18) = 6");

        // The `_<_` NumberOp produced a Truth result: 2 < 3 = tt.
        let lt = m.ops[&("_<_".to_string(), 2)];
        let (a, b) = (num(&mut m, 2), num(&mut m, 3));
        let q = m.engine.make_free(lt, vec![a, b]);
        let r = m.engine.reduce(q);
        let tt = m.ops[&("tt".to_string(), 0)];
        let tt_node = m.engine.make_const(tt);
        assert!(m.engine.deep_equal(r, tt_node), "2 < 3 = tt");
    }

    /// A nonbinary `assoc` declaration compiles as a free operator. Its syntax must use the same effective
    /// flag, or the grammar would incorrectly accept a flattened associative argument list for a ternary
    /// application.
    #[test]
    fn nonbinary_assoc_compiles_as_free_theory() {
        let mut module = build(
            "\
fmod BAD-ASSOC is
  sort S .
  op a : -> S .
  op f : S S S -> S [assoc] .
endfm
",
        );
        let f = module.ops[&("f".to_string(), 3)];
        let a = module.ops[&("a".to_string(), 0)];
        assert!(
            !module.syntax[&f].assoc,
            "compiled syntax must clear the invalid assoc attribute"
        );

        let a0 = module.engine.make_const(a);
        let inner = module.engine.make_free(f, vec![a0, a0, a0]);
        let root = module.engine.make_free(f, vec![a0, a0, inner]);
        assert!(matches!(
            module.engine.node(root).repr(),
            tnk_core::dag::NodeRepr::App
        ));
        assert_eq!(
            module.engine.node(root).children().collect::<Vec<_>>(),
            vec![a0, a0, inner],
            "free fallback preserves the ternary application rather than flattening it"
        );

        module.engine.reset_rewrites();
        let result = module.engine.reduce(root);
        assert_eq!(result, root);
        assert_eq!(module.engine.rewrites(), 0);
        assert_eq!(
            module.engine.sorts().name(module.engine.sort_of(result)),
            "S"
        );
    }

    #[test]
    fn constructor_analysis_rejects_mixed_overload_axioms() {
        let mut module = build(
            "\
fmod BAD-CTOR-OVERLOAD is
  sorts A B K .
  subsorts A B < K .
  ops a : -> A [ctor] .
  ops b : -> B [ctor] .
  op _*_ : A A -> A [ctor comm] .
  op _*_ : B B -> B [ctor assoc comm] .
endfm
",
        );
        let rejection = match ConstructorAnalysis::build(
            &mut module.engine,
            &SortOverrides::default(),
            false,
        ) {
            Ok(_) => panic!("mixed constructor axiom profiles must be rejected"),
            Err(rejection) => rejection,
        };
        assert!(matches!(
            rejection,
            EligibilityRejection::InconsistentOverloadedConstructorAxioms { .. }
        ));
    }

    #[test]
    fn cross_range_kind_overloads_use_distinct_symbols() {
        let cases = [
            "\
fmod SAME-DOMAIN-RANGE-KINDS is
  sorts A B C .
  op f : A -> B .
  op f : A -> C .
endfm
",
            "\
fmod INCOMPARABLE-DOMAIN-RANGE-KINDS is
  sorts A A1 A2 B C .
  subsorts A1 A2 < A .
  op f : A1 -> B .
  op f : A2 -> C .
endfm
",
        ];

        for source in cases {
            let module = build(source);
            let profiles = module
                .op_profiles
                .iter()
                .filter(|profile| module.engine.symbol(profile.symbol).name() == "f")
                .collect::<Vec<_>>();
            let [left, right] = profiles.as_slice() else {
                panic!("expected exactly two source profiles for f");
            };
            assert_ne!(
                left.symbol, right.symbol,
                "different range kinds must not share one kernel symbol"
            );
            let sorts = module.engine.sorts();
            assert_ne!(
                sorts.kind_of(left.range),
                sorts.kind_of(right.range),
                "the fixture must exercise distinct range kinds"
            );
            for profile in &profiles {
                let range_kind = sorts.kind_of(profile.range);
                assert!(
                    profiles
                        .iter()
                        .filter(|other| other.symbol == profile.symbol)
                        .all(|other| sorts.kind_of(other.range) == range_kind),
                    "a symbol declaration group must have one range kind"
                );
            }
        }
    }
}
