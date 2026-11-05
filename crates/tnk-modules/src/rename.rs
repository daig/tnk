//! Apply a renaming `* (sort A to B, op f to g)` to a flattened declaration bundle.
//!
//! Sort renaming substitutes the sort name everywhere it can appear: the `sorts`/`subsorts` lists, op
//! domains/ranges, variable sorts, and (as a token) inside statement bubbles. Op renaming replaces the
//! name of each matching op declaration. Term bubbles (statement sides, identities, term hooks, strategy
//! terms) are rewritten *grammar-aware*, because operator identity is not textual — an operator comma and
//! an argument separator are the same token (`delete(E, (E, S))`, `if E in S' then E, A else A fi`): build
//! the source module's parser ([`ViewOpSubst`]), parse each bubble, and re-emit each renamed operator
//! application in the target operator's syntax. A condition is split as the condition parser splits it, and
//! each of its terms is rewritten the same way. Only a bubble without a usable source parse falls back to
//! token-level renaming: exact-text single-token names, plus literal-anchored mixfix occurrences with
//! single-token arguments when the bubble does not parse at all. Optional attributes on a renaming override
//! the target operator's precedence, gathering, and strategy metadata.

use std::collections::{HashMap, HashSet};
use tnk_frontend::lex::{Frag, Interner, Sym, Token, split_mixfix, tokenize};
use tnk_frontend::load::{ConditionPiece, condition_pieces};
use tnk_frontend::rename_terms::{
    OpRenamer, ReconTarget, ViewOpMap, ViewOpSubst, rewrite_op_hook_signature_by,
};
use tnk_frontend::surface::ast::{Attrs, ModuleKind, PreModule, RenameItem, Statement, StratExpr};

use crate::flatten::FlatDecls;

/// One `op … to …` renaming, resolved. `dom_range` (`Some((domain, range))`, from `op f : A B -> C to g`)
/// restricts the rename to the overload family of `from` that the source profile names: every
/// declaration of `from` with that arity whose sorts lie in the profile's kinds. `None` renames every
/// overload. `attrs` overrides the target op's attributes.
struct OpRenameSpec {
    from: String,
    to: String,
    dom_range: Option<(Vec<String>, String)>,
    attrs: Attrs,
}

/// Rewrite `d` under the renaming `items`. The grammar-aware mixfix path may fail to build the source
/// module's parser, which is surfaced as an `Err`.
pub fn apply_renaming(
    mut d: FlatDecls,
    items: &[RenameItem],
    interner: &mut Interner,
) -> Result<FlatDecls, String> {
    let mut sort_map: HashMap<String, String> = HashMap::new();
    // Every op rename, as an [`OpRenameSpec`] (from/to canonical names, optional disambiguating signature,
    // attribute override). Statement labels rename separately (`label l to m`).
    let mut op_renames: Vec<OpRenameSpec> = Vec::new();
    let mut label_map: HashMap<String, String> = HashMap::new();
    for item in items {
        match item {
            RenameItem::Sort { from, to } => {
                sort_map.insert(from.clone(), to.clone());
            }
            RenameItem::Op {
                from,
                to,
                dom_range,
                attrs,
            } => {
                op_renames.push(OpRenameSpec {
                    from: from.clone(),
                    to: to.clone(),
                    dom_range: dom_range.clone(),
                    attrs: attrs.clone(),
                });
            }
            RenameItem::Label { from, to } => {
                label_map.insert(from.clone(), to.clone());
            }
        }
    }

    // Reconstruct every operator map structurally from the source parse. This handles fixity changes and
    // lets signature-qualified constant and mixfix renames expand to any target token shape.
    let structural_maps: Vec<ViewOpMap> = op_renames
        .iter()
        .map(|s| ViewOpMap {
            source: s.from.clone(),
            dom_range: s.dom_range.clone(),
            target: ReconTarget::Op(s.to.clone()),
        })
        .collect();
    let structural = ViewOpSubst::new(&premodule_of(&d), &structural_maps, interner)?;
    let grammar_renames: Vec<(String, Option<usize>, String)> = op_renames
        .iter()
        .filter(|s| s.dom_range.is_some())
        .map(|s| {
            (
                s.from.clone(),
                s.dom_range.as_ref().map(|(d, _)| d.len()),
                s.to.clone(),
            )
        })
        .collect();
    let renamer = OpRenamer::new(&premodule_of(&d), &grammar_renames, interner)?;

    // Single-token op map (textual). Applied to statement bubbles and `id:` identity bubbles.
    let single_op_map: HashMap<String, String> = op_renames
        .iter()
        .filter(|s| s.dom_range.is_none() && is_single_token(&s.from, interner))
        .map(|s| (s.from.clone(), s.to.clone()))
        .collect();

    rename_each(&mut d.sorts, &sort_map);
    for chain in &mut d.subsorts {
        for group in chain {
            rename_each(group, &sort_map);
        }
    }
    for op in &mut d.ops {
        // Snapshot the pre-rename signature so a signature-qualified rename selects against the source
        // sorts (a sort rename in the same renaming may rewrite the domain below).
        let orig_domain = op.domain.clone();
        let orig_range = op.range.clone();
        rename_each(&mut op.domain, &sort_map);
        if let Some(t) = sort_map.get(&op.range) {
            op.range = t.clone();
        }
        let canon: String = op.name.iter().map(|t| interner.resolve(t.sym)).collect();
        // Find the rename spec for this declaration. A signature-qualified spec selects the overload family
        // its profile names (every declaration of the name and arity whose sorts lie in the profile's
        // kinds), the family whose applications the statement rewrite follows by symbol; it takes precedence
        // over a plain spec, which matches every overload of the name.
        let selects = |profile: &(Vec<String>, String)| {
            structural
                .as_ref()
                .is_some_and(|r| r.selects_family(profile, &orig_domain, &orig_range))
        };
        let qualified = op_renames
            .iter()
            .find(|s| s.from == canon && s.dom_range.as_ref().is_some_and(selects));
        if let Some(spec) = qualified.or_else(|| {
            op_renames
                .iter()
                .find(|s| s.from == canon && s.dom_range.is_none())
        }) {
            // Preserve a separated OO attribute suffix so renamed attributes retain `b : value` spacing.
            let spaced_attribute_suffix = op.name.len() > 1 && canon.ends_with(":_");
            let suffix = spaced_attribute_suffix.then(|| {
                let n = op.name.len();
                [op.name[n - 2], op.name[n - 1]]
            });
            op.name = tokenize(&spec.to, interner);
            if let (Some(suffix), Some(label)) = (suffix, spec.to.strip_suffix(":_")) {
                op.name = tokenize(label, interner);
                op.name.extend(suffix);
            }
            apply_attr_override(&mut op.attrs, &spec.attrs);
        }
        // Identity attributes are arbitrary ground terms: rewrite their operator occurrences through
        // the same grammar-aware path as statements, then apply textual sort renames.
        if let Some(idb) = &mut op.attrs.id {
            rename_ops(
                idb,
                structural.as_ref(),
                renamer.as_ref(),
                &single_op_map,
                interner,
            );
            subst_sort_tokens(idb, &sort_map, interner);
        }
        // Hook signatures refer to other operators by name and profile, so renaming a referenced operator
        // must update the hook; a signature-qualified rename selects the hook reference by the same family
        // test as the declarations. Sorts in hook signatures and constants in term hooks follow the same
        // renaming.
        if let Some(sp) = &mut op.attrs.special {
            for (_purpose, toks) in &mut sp.op_hooks {
                *toks = rewrite_op_hook_signature_by(
                    toks,
                    &structural_maps,
                    |profile, domain, range| {
                        structural
                            .as_ref()
                            .is_some_and(|r| r.selects_family(profile, domain, range))
                    },
                    interner,
                );
                subst_sort_tokens(toks, &sort_map, interner);
            }
            for (_purpose, toks) in &mut sp.term_hooks {
                rename_ops(
                    toks,
                    structural.as_ref(),
                    renamer.as_ref(),
                    &single_op_map,
                    interner,
                );
                subst_sort_tokens(toks, &sort_map, interner);
            }
        }
    }
    for v in &mut d.vars {
        if let Some(t) = sort_map.get(&v.sort) {
            v.sort = t.clone();
        }
    }

    // Constants whose (final) range sort is a rename *target* are instance-specific (`nil : -> NatList`,
    // the renamed `none : -> QidSet`): two instantiations of the same parameterized module (`NAT-LIST` +
    // `QID-LIST` in `META-MODULE`) share the constant's name across distinct kinds, so a bare `nil` in an
    // inlined equation parses ambiguously once both are merged. Sort-qualify each such occurrence as
    // `(nil).NatList` — the parse-time kind selector is a no-op on the built term but disambiguates the
    // overload. (The flattener already inlines *variables* as colon-vars for the same reason; this is the
    // constant analogue.) Only renamed-sort constants are touched, so base constants (`true`, `0`) are not.
    let targets: HashSet<&String> = sort_map.values().collect();
    let const_qual: HashMap<String, Vec<Token>> = d
        .ops
        .iter()
        .filter(|op| op.domain.is_empty() && targets.contains(&op.range))
        .map(|op| {
            let name: String = op.name.iter().map(|t| interner.resolve(t.sym)).collect();
            // `c` → `( c ) .Sort` with the dotted sort lexed as the qualifier grammar expects
            // (`.NatList`, or `.List`,`{`,`Nat`,`}` for a structured target).
            let suffix = tokenize(&format!(") .{}", op.range), interner);
            (name, suffix)
        })
        .collect();
    let lparen = tokenize("(", interner);
    for op in &mut d.ops {
        if let Some(idb) = &mut op.attrs.id {
            *idb = qualify_constants(idb, &const_qual, &lparen, interner);
        }
    }

    // Statement bubbles: op renames (mixfix grammar-aware, then textual sorts/single ops), then constant
    // qualification.
    for st in &mut d.statements {
        match st {
            Statement::Eq { lhs, rhs, cond, .. } => {
                rewrite_term(
                    lhs,
                    structural.as_ref(),
                    renamer.as_ref(),
                    &sort_map,
                    &single_op_map,
                    &const_qual,
                    &lparen,
                    interner,
                );
                rewrite_term(
                    rhs,
                    structural.as_ref(),
                    renamer.as_ref(),
                    &sort_map,
                    &single_op_map,
                    &const_qual,
                    &lparen,
                    interner,
                );
                if let Some(c) = cond {
                    rewrite_cond(
                        c,
                        structural.as_ref(),
                        renamer.as_ref(),
                        &sort_map,
                        &single_op_map,
                        &const_qual,
                        &lparen,
                        interner,
                    );
                }
            }
            Statement::Mb {
                lhs, sort, cond, ..
            } => {
                rewrite_term(
                    lhs,
                    structural.as_ref(),
                    renamer.as_ref(),
                    &sort_map,
                    &single_op_map,
                    &const_qual,
                    &lparen,
                    interner,
                );
                subst_sort_tokens(sort, &sort_map, interner);
                if let Some(c) = cond {
                    rewrite_cond(
                        c,
                        structural.as_ref(),
                        renamer.as_ref(),
                        &sort_map,
                        &single_op_map,
                        &const_qual,
                        &lparen,
                        interner,
                    );
                }
            }
            Statement::Rule { lhs, rhs, cond, .. } => {
                rewrite_term(
                    lhs,
                    structural.as_ref(),
                    renamer.as_ref(),
                    &sort_map,
                    &single_op_map,
                    &const_qual,
                    &lparen,
                    interner,
                );
                rewrite_term(
                    rhs,
                    structural.as_ref(),
                    renamer.as_ref(),
                    &sort_map,
                    &single_op_map,
                    &const_qual,
                    &lparen,
                    interner,
                );
                if let Some(c) = cond {
                    rewrite_cond(
                        c,
                        structural.as_ref(),
                        renamer.as_ref(),
                        &sort_map,
                        &single_op_map,
                        &const_qual,
                        &lparen,
                        interner,
                    );
                }
            }
        }
    }

    let rename_identity = format!("{items:?}");
    for decl in &mut d.strat_decls {
        rename_each(&mut decl.domain, &sort_map);
        if let Some(to) = sort_map.get(&decl.subject) {
            decl.subject = to.clone();
        }
        decl.home = None;
        if let Some(origin) = &mut decl.origin {
            origin.push_str(&rename_identity);
        }
    }
    for def in &mut d.strat_defs {
        def.home = None;
        if let Some(origin) = &mut def.origin {
            origin.push_str(&rename_identity);
        }
        for param in &mut def.params {
            rewrite_term(
                param,
                structural.as_ref(),
                renamer.as_ref(),
                &sort_map,
                &single_op_map,
                &const_qual,
                &lparen,
                interner,
            );
        }
        rewrite_strategy_expr(
            &mut def.body,
            structural.as_ref(),
            renamer.as_ref(),
            &sort_map,
            &single_op_map,
            &const_qual,
            &lparen,
            &label_map,
            interner,
        );
        if let Some(cond) = &mut def.cond {
            rewrite_cond(
                cond,
                structural.as_ref(),
                renamer.as_ref(),
                &sort_map,
                &single_op_map,
                &const_qual,
                &lparen,
                interner,
            );
        }
    }
    // Statement-label renames (`label l to m`): rewrite the label field of each statement (rule/eq/mb).
    if !label_map.is_empty() {
        for st in &mut d.statements {
            let (Statement::Eq { label, .. }
            | Statement::Mb { label, .. }
            | Statement::Rule { label, .. }) = st;
            if let Some(l) = label
                && let Some(to) = label_map.get(l)
            {
                *l = to.clone();
            }
        }
    }
    Ok(d)
}

/// Rename every term-bearing leaf of a strategy expression. Strategy names are unchanged because ordinary
/// operator renamings do not target them.
#[allow(clippy::too_many_arguments)]
fn rewrite_strategy_expr(
    expr: &mut StratExpr,
    structural: Option<&ViewOpSubst>,
    renamer: Option<&OpRenamer>,
    sort_map: &HashMap<String, String>,
    single_op_map: &HashMap<String, String>,
    const_qual: &HashMap<String, Vec<Token>>,
    lparen: &[Token],
    label_map: &HashMap<String, String>,
    interner: &mut Interner,
) {
    let mut rewrite_term_bubble = |bubble: &mut Vec<Token>| {
        rewrite_term(
            bubble,
            structural,
            renamer,
            sort_map,
            single_op_map,
            const_qual,
            lparen,
            interner,
        );
    };
    match expr {
        StratExpr::Idle | StratExpr::Fail | StratExpr::All => {}
        StratExpr::Apply {
            label,
            subst,
            substrats,
        } => {
            if let Some(to) = label_map.get(label) {
                *label = to.clone();
            }
            for (variable, value) in subst {
                rewrite_term_bubble(variable);
                rewrite_term_bubble(value);
            }
            for child in substrats {
                rewrite_strategy_expr(
                    child,
                    structural,
                    renamer,
                    sort_map,
                    single_op_map,
                    const_qual,
                    lparen,
                    label_map,
                    interner,
                );
            }
        }
        StratExpr::Top(child)
        | StratExpr::One(child)
        | StratExpr::Star(child)
        | StratExpr::Plus(child)
        | StratExpr::Normalize(child) => {
            rewrite_strategy_expr(
                child,
                structural,
                renamer,
                sort_map,
                single_op_map,
                const_qual,
                lparen,
                label_map,
                interner,
            );
        }
        StratExpr::Seq(left, right) | StratExpr::Union(left, right) => {
            rewrite_strategy_expr(
                left,
                structural,
                renamer,
                sort_map,
                single_op_map,
                const_qual,
                lparen,
                label_map,
                interner,
            );
            rewrite_strategy_expr(
                right,
                structural,
                renamer,
                sort_map,
                single_op_map,
                const_qual,
                lparen,
                label_map,
                interner,
            );
        }
        StratExpr::Branch {
            test,
            success,
            failure,
        } => {
            for child in [test, success, failure] {
                rewrite_strategy_expr(
                    child,
                    structural,
                    renamer,
                    sort_map,
                    single_op_map,
                    const_qual,
                    lparen,
                    label_map,
                    interner,
                );
            }
        }
        StratExpr::Test { pattern, cond, .. } => {
            rewrite_term_bubble(pattern);
            if let Some(cond) = cond {
                rewrite_cond(
                    cond,
                    structural,
                    renamer,
                    sort_map,
                    single_op_map,
                    const_qual,
                    lparen,
                    interner,
                );
            }
        }
        StratExpr::MatchRew {
            pattern,
            cond,
            subs,
            ..
        } => {
            rewrite_term_bubble(pattern);
            for (variable, _) in subs.iter_mut() {
                rewrite_term_bubble(variable);
            }
            if let Some(cond) = cond {
                rewrite_cond(
                    cond,
                    structural,
                    renamer,
                    sort_map,
                    single_op_map,
                    const_qual,
                    lparen,
                    interner,
                );
            }
            for (_, child) in subs {
                rewrite_strategy_expr(
                    child,
                    structural,
                    renamer,
                    sort_map,
                    single_op_map,
                    const_qual,
                    lparen,
                    label_map,
                    interner,
                );
            }
        }
        StratExpr::Sugar { args, .. } => {
            for child in args {
                rewrite_strategy_expr(
                    child,
                    structural,
                    renamer,
                    sort_map,
                    single_op_map,
                    const_qual,
                    lparen,
                    label_map,
                    interner,
                );
            }
        }
        StratExpr::Call { args, .. } => {
            for arg in args {
                rewrite_term_bubble(arg);
            }
        }
    }
}

/// Expand each bare constant occurrence `c` (a key of `const_qual`) into the sort-qualified `( c ) .Sort`
/// to disambiguate overloads shared across instantiations. The left-to-right pass emits each matched input
/// token once without rescanning it.
fn qualify_constants(
    b: &[Token],
    const_qual: &HashMap<String, Vec<Token>>,
    lparen: &[Token],
    interner: &Interner,
) -> Vec<Token> {
    if const_qual.is_empty() {
        return b.to_vec();
    }
    let mut out = Vec::with_capacity(b.len());
    for (index, t) in b.iter().enumerate() {
        let already_qualified = index > 0
            && index + 2 < b.len()
            && interner.resolve(b[index - 1].sym) == "("
            && interner.resolve(b[index + 1].sym) == ")"
            && interner.resolve(b[index + 2].sym).starts_with('.');
        if !already_qualified && let Some(suffix) = const_qual.get(interner.resolve(t.sym)) {
            out.extend_from_slice(lparen);
            out.push(*t);
            out.extend_from_slice(suffix);
        } else {
            out.push(*t);
        }
    }
    out
}

/// Rewrite one term bubble: op renames first (on the pre-rename bubble, via the source parser; see
/// [`rename_ops`]), then textual sort renames, then constant qualification.
#[allow(clippy::too_many_arguments)]
fn rewrite_term(
    b: &mut Vec<Token>,
    structural: Option<&ViewOpSubst>,
    renamer: Option<&OpRenamer>,
    sort_map: &HashMap<String, String>,
    single_op_map: &HashMap<String, String>,
    const_qual: &HashMap<String, Vec<Token>>,
    lparen: &[Token],
    interner: &mut Interner,
) {
    rename_ops(b, structural, renamer, single_op_map, interner);
    subst_sort_tokens(b, sort_map, interner);
    *b = qualify_constants(b, const_qual, lparen, interner);
}

/// Apply every op rename to one term bubble exactly once. When structural reconstruction rewrote the
/// bubble from its source parse, every mapped occurrence (single-token, mixfix, and signature-qualified)
/// has been rewritten, so the token-level paths must not run again: a remaining source spelling is not an
/// occurrence. Re-applying a map to reconstructed output breaks swaps and chains (`op f to g, op g to
/// f`), and the arity-keyed [`OpRenamer`] would also rename a same-arity overload in another kind that a
/// signature-qualified rename deliberately left alone. Only a bubble without such a parse takes the
/// token-level paths.
fn rename_ops(
    b: &mut Vec<Token>,
    structural: Option<&ViewOpSubst>,
    renamer: Option<&OpRenamer>,
    single_op_map: &HashMap<String, String>,
    interner: &mut Interner,
) {
    if let Some(r) = structural {
        let (rewritten, reconstructed) = r.rewrite_checked(b, interner);
        *b = rewritten;
        if reconstructed {
            return;
        }
    }
    if let Some(r) = renamer {
        *b = r.rewrite(b, interner);
    }
    subst_tokens(b, single_op_map, interner);
}

/// Rewrite a condition bubble term by term. A whole condition is not a term, so it has no source parse to
/// reconstruct. The bubble is split exactly as the condition parser splits it ([`condition_pieces`]): each
/// term (a side of `=`, `:=`, or `=>`, the subject of a sort test, or a bare Boolean fragment) is rewritten
/// as a term bubble ([`rewrite_term`]), a sort test's sort takes only the sort renames, and the connectives
/// are kept.
#[allow(clippy::too_many_arguments)]
fn rewrite_cond(
    b: &mut Vec<Token>,
    structural: Option<&ViewOpSubst>,
    renamer: Option<&OpRenamer>,
    sort_map: &HashMap<String, String>,
    single_op_map: &HashMap<String, String>,
    const_qual: &HashMap<String, Vec<Token>>,
    lparen: &[Token],
    interner: &mut Interner,
) {
    let mut out = Vec::with_capacity(b.len());
    for piece in condition_pieces(b, interner) {
        match piece {
            ConditionPiece::Term(term) => {
                let mut term = term.to_vec();
                rewrite_term(
                    &mut term,
                    structural,
                    renamer,
                    sort_map,
                    single_op_map,
                    const_qual,
                    lparen,
                    interner,
                );
                out.extend(term);
            }
            ConditionPiece::Sort(sort) => {
                let mut sort = sort.to_vec();
                subst_sort_tokens(&mut sort, sort_map, interner);
                out.extend(sort);
            }
            ConditionPiece::Separator(token) => out.push(token),
        }
    }
    *b = out;
}

/// A `PreModule` carrying `d`'s declarations (for building the source parser). Fully flattened, so it has
/// no imports/parameters; system-kind so any rule bubbles parse.
fn premodule_of(d: &FlatDecls) -> PreModule {
    PreModule {
        name: "$RENAME-SRC".to_string(),
        source_line: None,
        diagnostics: Vec::new(),
        kind: ModuleKind::System,
        is_theory: false,
        is_strategy: false,
        // This temporary module exists only to build the source grammar; no statements execute here, so
        // object-pattern completion is irrelevant.
        is_object: false,
        object_statements: Vec::new(),
        params: Vec::new(),
        imports: Vec::new(),
        sorts: d.sorts.clone(),
        subsorts: d.subsorts.clone(),
        ops: d.ops.clone(),
        vars: d.vars.clone(),
        statements: d.statements.clone(),
        strat_decls: Vec::new(),
        strat_defs: Vec::new(),
    }
}

/// Whether `name` is a single-token op name (a constant or prefix operator — no holes).
fn is_single_token(name: &str, interner: &mut Interner) -> bool {
    let frags = split_mixfix(name, interner);
    frags.len() == 1 && matches!(frags[0], Frag::Tok(_))
}

/// Replace the target operator's precedence, gathering, and strategy attributes when the renaming supplies
/// corresponding overrides.
fn apply_attr_override(attrs: &mut Attrs, ovr: &Attrs) {
    if ovr.prec.is_some() {
        attrs.prec = ovr.prec;
    }
    if ovr.gather.is_some() {
        attrs.gather = ovr.gather.clone();
    }
    if ovr.strat.is_some() {
        attrs.strat = ovr.strat.clone();
    }
}

/// Replace each string in `xs` that is a key of `map` with its mapped value.
fn rename_each(xs: &mut [String], map: &HashMap<String, String>) {
    for x in xs {
        if let Some(t) = map.get(x) {
            *x = t.clone();
        }
    }
}

/// Replace each token whose text is a key of `map` with the re-interned target (kind/line preserved).
fn subst_tokens(bubble: &mut [Token], map: &HashMap<String, String>, interner: &mut Interner) {
    for t in bubble {
        let text = interner.resolve(t.sym).to_string();
        if let Some(to) = map.get(&text) {
            t.sym = interner.intern(to);
        } else if let Some((base, count)) = text.rsplit_once('^')
            && !base.is_empty()
            && !count.is_empty()
            && count.bytes().all(|b| b.is_ascii_digit())
            && let Some(to) = map.get(base)
        {
            // An iter application is one lexical token (`g^1000000`), but the renamed symbol is its
            // `g` prefix. Preserve the scalar count while re-rooting the identity/statement at the target
            // operator; treating the whole token as a stale source name makes copied compact identities
            // fail to parse after `op g to h`.
            t.sym = interner.intern(&format!("{to}^{count}"));
        } else if let Some((name, sort)) = text.rsplit_once(':')
            && !name.is_empty()
            && let Some(to) = map.get(sort)
        {
            // A glued colon variable stores its sort inside the same token. Rename that component
            // (`A:Elt ↦ A:Item`) because the whole-token branch cannot see the suffix separately.
            t.sym = interner.intern(&format!("{name}:{to}"));
        }
    }
}

/// Replace sort names in a token bubble, including structured spellings split by the lexer
/// (`Vector{Int0}` -> `Vector`, `{`, `Int0`, `}`), dotted sort qualifiers, and colon variables.
fn subst_sort_tokens(
    bubble: &mut Vec<Token>,
    map: &HashMap<String, String>,
    interner: &mut Interner,
) {
    struct Mapping {
        source: Vec<Sym>,
        target: Vec<Token>,
        source_name: String,
        target_name: String,
    }

    let mut mappings = Vec::with_capacity(map.len() * 2);
    for (from, to) in map {
        for dotted in [false, true] {
            let source_text = if dotted {
                format!(".{from}")
            } else {
                from.clone()
            };
            let target_text = if dotted { format!(".{to}") } else { to.clone() };
            mappings.push(Mapping {
                source: tokenize(&source_text, interner)
                    .into_iter()
                    .map(|token| token.sym)
                    .collect(),
                target: tokenize(&target_text, interner),
                source_name: from.clone(),
                target_name: to.clone(),
            });
        }
    }
    mappings.sort_by(|left, right| {
        right
            .source
            .len()
            .cmp(&left.source.len())
            .then_with(|| left.source_name.cmp(&right.source_name))
    });

    let mut index = 0;
    while index < bubble.len() {
        // The lexer keeps an on-the-fly variable with a structured sort as one identifier token
        // (`L:List{Nat}`), while `tokenize("List{Nat}")` below necessarily yields several tokens.
        // Handle that exact suffix before the token-sequence matcher.
        if let Some((name, sort)) = interner.resolve(bubble[index].sym).rsplit_once(':')
            && !name.is_empty()
            && let Some(target) = map.get(sort)
        {
            bubble[index].sym = interner.intern(&format!("{name}:{target}"));
            index += 1;
            continue;
        }
        let exact = mappings.iter().find(|mapping| {
            index + mapping.source.len() <= bubble.len()
                && bubble[index..index + mapping.source.len()]
                    .iter()
                    .map(|token| token.sym)
                    .eq(mapping.source.iter().copied())
        });
        let colon = if exact.is_none() {
            let text = interner.resolve(bubble[index].sym);
            text.split_once(':').and_then(|(name, first)| {
                mappings.iter().find_map(|mapping| {
                    let source_first = mapping.source.first().map(|&sym| interner.resolve(sym))?;
                    let rest = &mapping.source[1..];
                    (name.len() + first.len() + 1 == text.len()
                        && first == source_first
                        && index + 1 + rest.len() <= bubble.len()
                        && bubble[index + 1..index + 1 + rest.len()]
                            .iter()
                            .map(|token| token.sym)
                            .eq(rest.iter().copied()))
                    .then(|| (name.to_string(), mapping))
                })
            })
        } else {
            None
        };

        let (consumed, mut replacement) = if let Some(mapping) = exact {
            (mapping.source.len(), mapping.target.clone())
        } else if let Some((name, mapping)) = colon {
            (
                mapping.source.len(),
                tokenize(&format!("{name}:{}", mapping.target_name), interner),
            )
        } else {
            index += 1;
            continue;
        };
        let line = bubble[index].line;
        for token in &mut replacement {
            token.line = line;
        }
        let replacement_len = replacement.len();
        bubble.splice(index..index + consumed, replacement);
        index += replacement_len;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::flatten::FlatDecls;
    use tnk_frontend::surface::parser::Parser;

    fn empty() -> FlatDecls {
        FlatDecls {
            sorts: vec![],
            subsorts: vec![],
            ops: vec![],
            vars: vec![],
            statements: vec![],
            object_statements: vec![],
            strat_decls: vec![],
            strat_defs: vec![],
        }
    }

    /// A single-token op rename (a constant / prefix op) needs no grammar and applies textually.
    #[test]
    fn single_token_op_rename_ok() {
        let mut i = Interner::new();
        let single = [RenameItem::Op {
            from: "f".into(),
            to: "g".into(),
            dom_range: None,
            attrs: Attrs::default(),
        }];
        assert!(apply_renaming(empty(), &single, &mut i).is_ok());
    }

    /// Sort renaming rewrites the `sorts` list and op domains/ranges.
    #[test]
    fn sort_rename_rewrites_declarations() {
        let mut i = Interner::new();
        let mut d = empty();
        d.sorts = vec!["Elt".into()];
        let renamed = apply_renaming(
            d,
            &[RenameItem::Sort {
                from: "Elt".into(),
                to: "Item".into(),
            }],
            &mut i,
        )
        .expect("rename");
        assert_eq!(renamed.sorts, ["Item"]);
    }

    #[test]
    fn sort_rename_rewrites_structured_colon_variable() {
        let mut i = Interner::new();
        let mut bubble = tokenize("L:List{Nat}", &mut i);
        assert_eq!(bubble.len(), 1, "colon variable is one lexer token");
        subst_sort_tokens(
            &mut bubble,
            &HashMap::from([("List{Nat}".to_string(), "NatList".to_string())]),
            &mut i,
        );
        assert_eq!(i.resolve(bubble[0].sym), "L:NatList");
    }

    #[test]
    fn compound_identity_reconstructs_across_fixity_and_iter_renames() {
        let mut i = Interner::new();
        let tokens = tokenize(
            "fmod R is sort S . ops a b : -> S [ctor] . op g : S -> S [ctor iter] . \
             op pair : S S -> S [ctor] . \
             op join : S S -> S [assoc id: pair(g^1000000(a),b)] . endfm",
            &mut i,
        );
        let pm = Parser::new(&tokens, &i)
            .parse_source()
            .expect("parse")
            .modules
            .remove(0);
        let d = FlatDecls {
            sorts: pm.sorts,
            subsorts: pm.subsorts,
            ops: pm.ops,
            vars: pm.vars,
            object_statements: vec![false; pm.statements.len()],
            statements: pm.statements,
            strat_decls: pm.strat_decls,
            strat_defs: pm.strat_defs,
        };
        let op = |from: &str, to: &str| RenameItem::Op {
            from: from.into(),
            to: to.into(),
            dom_range: None,
            attrs: Attrs::default(),
        };
        let renamed = apply_renaming(
            d,
            &[
                RenameItem::Sort {
                    from: "S".into(),
                    to: "T".into(),
                },
                op("a", "x"),
                op("b", "y"),
                op("g", "h"),
                op("pair", "duo"),
                op("join", "merge"),
            ],
            &mut i,
        )
        .expect("rename");
        let join = renamed
            .ops
            .iter()
            .find(|op| op.name.iter().map(|t| i.resolve(t.sym)).collect::<String>() == "merge")
            .expect("join");
        let identity = join.attrs.id.as_ref().expect("identity");
        let text: String = identity.iter().map(|t| i.resolve(t.sym)).collect();
        assert_eq!(text, "duo(h^1000000((x).T),(y).T)");
        tnk_frontend::load::build_loaded_module(&premodule_of(&renamed), &mut i)
            .expect("renamed compound identity builds");
    }

    /// A profile selects an overload family (§1.2): with `Foo < Bar`, `f : Foo -> Foo` and `f : Bar -> Bar`
    /// are one family, so `op f : Foo -> Foo to g` renames both declarations, as the statement rewrite
    /// renames the family equation `f(B) = y`. Another family of the same name stays.
    #[test]
    fn profile_rename_selects_the_overload_family() {
        let mut i = Interner::new();
        let tokens = tokenize(
            "fmod BASH is sorts Foo Bar Baz . subsort Foo < Bar . op f : Foo -> Foo . \
             op f : Bar -> Bar . op f : Baz -> Baz . op y : -> Bar . var B : Bar . \
             eq f(B) = y . endfm",
            &mut i,
        );
        let pm = Parser::new(&tokens, &i)
            .parse_source()
            .expect("parse")
            .modules
            .remove(0);
        let d = FlatDecls {
            object_statements: vec![pm.is_object; pm.statements.len()],
            sorts: pm.sorts,
            subsorts: pm.subsorts,
            ops: pm.ops,
            vars: pm.vars,
            statements: pm.statements,
            strat_decls: pm.strat_decls,
            strat_defs: pm.strat_defs,
        };
        let renamed = apply_renaming(
            d,
            &[RenameItem::Op {
                from: "f".into(),
                to: "g".into(),
                dom_range: Some((vec!["Foo".into()], "Foo".into())),
                attrs: Attrs::default(),
            }],
            &mut i,
        )
        .expect("rename");
        let profiles: Vec<String> = renamed
            .ops
            .iter()
            .filter(|op| op.domain.len() == 1)
            .map(|op| {
                let name: String = op.name.iter().map(|t| i.resolve(t.sym)).collect();
                format!("{name} : {} -> {}", op.domain[0], op.range)
            })
            .collect();
        assert_eq!(
            profiles,
            ["g : Foo -> Foo", "g : Bar -> Bar", "f : Baz -> Baz"]
        );
        let Statement::Eq { lhs, .. } = &renamed.statements[0] else {
            panic!("equation");
        };
        let lhs: String = lhs.iter().map(|t| i.resolve(t.sym)).collect();
        assert_eq!(lhs, "g(B)");
    }

    /// A reconstructed identity bubble is final: the textual single-token pass must not apply a swap a
    /// second time (`pair(a, b)` under `op a to b, op b to a` is `pair(b, a)`, not the original).
    #[test]
    fn swapped_constants_rename_identity_once() {
        let mut i = Interner::new();
        let tokens = tokenize(
            "fmod SWAP-ID is sort S . ops a b : -> S [ctor] . op pair : S S -> S [ctor] . \
             op join : S S -> S [assoc id: pair(a, b)] . endfm",
            &mut i,
        );
        let pm = Parser::new(&tokens, &i)
            .parse_source()
            .expect("parse")
            .modules
            .remove(0);
        let d = FlatDecls {
            object_statements: vec![pm.is_object; pm.statements.len()],
            sorts: pm.sorts,
            subsorts: pm.subsorts,
            ops: pm.ops,
            vars: pm.vars,
            statements: pm.statements,
            strat_decls: pm.strat_decls,
            strat_defs: pm.strat_defs,
        };
        let op = |from: &str, to: &str| RenameItem::Op {
            from: from.into(),
            to: to.into(),
            dom_range: None,
            attrs: Attrs::default(),
        };
        let renamed = apply_renaming(d, &[op("a", "b"), op("b", "a")], &mut i).expect("rename");
        let join = renamed
            .ops
            .iter()
            .find(|op| op.name.iter().map(|t| i.resolve(t.sym)).collect::<String>() == "join")
            .expect("join");
        let identity = join.attrs.id.as_ref().expect("identity");
        let text: String = identity.iter().map(|t| i.resolve(t.sym)).collect();
        assert_eq!(text, "pair(b,a)");
    }
}
