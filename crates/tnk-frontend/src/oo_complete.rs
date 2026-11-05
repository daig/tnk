//! Object-pattern completion for parsed object-module terms. The
//! transformer runs in [`load_statements`](crate::load) on parsed [`Term`]s before compilation into
//! engine equations and rules: on every statement of an **object module** (`omod`/`oth`), the
//! statements it imports included, and on every statement that an object module donates to a
//! non-object importer (see `PreModule::completes_object_patterns`). Reflection parses `[nonexec]`
//! statements through the same gate, so they are completed like executable ones.
//!
//! For each object pattern `< O : C | atts >` in a statement, completion makes the statement match objects
//! that carry *more* than the mentioned attributes, and rules written for a class apply to its subclasses:
//!
//! 1. **Class constant → variable.** If `C` is a class *constant* (an arity-0 ctor ranging on a class
//!    sort — a strict subsort of `Cid`), every occurrence of this object (LHS + RHS/condition) has `C`
//!    replaced by one fresh variable `V:C`. A `V:C` matches any subclass constant (`Savings < Account`),
//!    so the rule is subclass-polymorphic. A class *variable* is left alone.
//! 2. **Attribute-set variable.** The LHS (pattern) object gets a fresh `Atts:AttributeSet` variable
//!    spliced into its attribute set (`bal : N` → `bal : N, Atts`), capturing the object's *other*
//!    attributes; each RHS/condition occurrence of the same object gets that **same** `Atts` variable, so
//!    the extra attributes are carried through.
//! 3. **Missing / extra attributes.** An attribute in the pattern but absent from an RHS occurrence is
//!    copied back to it (so it is preserved); an attribute in some RHS occurrence but absent from the
//!    pattern is added to the pattern as a fresh kind-variable attribute `a(A:[K])` (so the LHS matches
//!    objects that already carry it).
//!
//! Completion is gated structurally: it fires only on object patterns whose class argument is a class
//! constant or class-sorted variable. CONFIGURATION's `getClass` equation (`< O : C:Cid | A >`, where
//! `Cid` is not a class sort) and other non-object statements pass through unchanged. The pass is enabled
//! only for the statements selected above; its structural gate also makes it a no-op for ineligible
//! statements.
//!
//! Every RHS/condition occurrence of an object must carry the pattern occurrence's class argument (the
//! same class constant or class variable). A statement that changes an object's class is left exactly as
//! written, like a statement that fails any other gate: replacing the written class with `V:C` would
//! discard the class change, and keeping it would carry one class's other attributes into another.
//! Likewise, every element of the attribute set of a pattern occurrence, or of another occurrence of
//! that object, must be a unary attribute term `a(v)`, `none`, or the one attribute-set variable. Any
//! other element (an `Attribute` constant, a non-unary operator) leaves the statement as written, because
//! step 3 can add only a unary `a(A:[K])` to the pattern. An object first seen on a RHS or in a condition
//! is a new object: its own class argument and attribute-set elements are neither checked nor changed.

use std::collections::HashMap;

use tnk_core::engine::OoInfo;
use tnk_core::sort::SortId;
use tnk_core::symbol::SymbolId;
use tnk_core::term::{ConditionFragment, Term, Var};

use crate::build_term::VarIndex;
use crate::sig::syntax::BuiltModule;

/// Position of an object occurrence, determining how completion rewrites it.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Mode {
    /// The statement's left-hand side (and its own object patterns) — the *defining* occurrence.
    Pattern,
    /// A right-hand side or a condition *subject* — carries the shared attribute-set variable.
    Subject,
    /// A condition *pattern* (`:=` lhs, rewrite-condition rhs). An object here disables completion.
    CondPattern,
}

/// One object occurrence's attribute set, decomposed: the individual attribute terms (keyed by their head
/// operator, first-seen order) and the attribute-set variable, if the source already wrote one.
struct Occ {
    attrs: Vec<(SymbolId, Term)>,
    set_var: Option<Var>,
}

/// The gathered facts about one object identity (all occurrences sharing an object name `O`).
struct ObjInfo {
    /// The object name (`arg 0`) — the identity key.
    oid: Term,
    /// The class sort (a strict subsort of `Cid`): the sort of `V` if the class is a constant, or the
    /// declared sort of the class variable.
    class_sort: SortId,
    /// The class argument's variable index when it is already a class-sorted variable; `None` when it is
    /// a class constant that completion replaces with a fresh `V:class_sort` in every occurrence. A
    /// class variable used elsewhere in the statement disables completion.
    class_var: Option<u32>,
    /// The pattern occurrence's class argument, which every subject occurrence must repeat.
    class_arg: Term,
    pattern: Occ,
    subjects: Vec<Occ>,
}

/// The precomputed rewrite for one object identity (fresh variables allocated once, applied per occurrence).
struct ObjPlan {
    /// The fresh class variable term to place at `arg 1`, if the class argument was a constant.
    class_replace: Option<Term>,
    /// The attribute-set variable term appended to every occurrence (the existing pattern one, or a fresh
    /// `Atts`).
    atts_var: Term,
    /// Existing and added pattern attributes, used to restore attributes missing from a subject occurrence.
    pattern_attrs: Vec<(SymbolId, Term)>,
    /// Kind-variable attributes to add to the LHS pattern (attributes some RHS has but the pattern lacks).
    added_attrs: Vec<(SymbolId, Term)>,
}

/// Run object-pattern completion on one statement's terms in place. `lhs` is the pattern; `rhs` the
/// right-hand side (equations/rules; `None` for memberships); `cond` the condition fragments. Fresh
/// variables are allocated into `vars` (so the caller's `nr_vars` must be read *after* this runs). A no-op
/// unless the statement contains an object pattern with a class-sorted class argument.
pub fn complete_statement(
    info: &OoInfo,
    m: &BuiltModule,
    vars: &mut VarIndex,
    lhs: &mut Term,
    rhs: Option<&mut Term>,
    cond: &mut [ConditionFragment],
) -> bool {
    // --- Gather (immutable walk over lhs / rhs / condition). ---
    let mut objs: Vec<ObjInfo> = Vec::new();
    let mut ignore = false;
    gather(lhs, Mode::Pattern, info, m, &mut objs, &mut ignore);
    if let Some(rhs) = &rhs {
        gather(rhs, Mode::Subject, info, m, &mut objs, &mut ignore);
    }
    for frag in cond.iter() {
        gather_condition(frag, info, m, &mut objs, &mut ignore);
    }
    if ignore || objs.is_empty() {
        return false;
    }
    if !check_variables(&objs, lhs, rhs.as_deref(), cond) {
        return false;
    }
    // Report a change only when completion adds or replaces something. A class-polymorphic object that
    // already carries the shared attribute-set variable, with identical attribute keys in every
    // occurrence, is already complete.
    let needs_completion = objs.iter().any(|obj| {
        obj.class_var.is_none()
            || obj.pattern.set_var.is_none()
            || obj.subjects.iter().any(|subject| {
                obj.pattern
                    .attrs
                    .iter()
                    .any(|(symbol, _)| !subject.attrs.iter().any(|(other, _)| other == symbol))
                    || subject.attrs.iter().any(|(symbol, _)| {
                        !obj.pattern.attrs.iter().any(|(other, _)| other == symbol)
                    })
            })
    });
    if !needs_completion {
        return false;
    }

    // --- Plan (allocate fresh variables per object: V, then Atts, then kind-var A's). ---
    let mut plans: HashMap<Term, ObjPlan> = HashMap::new();
    for obj in &objs {
        // Class constant → a fresh `V:class_sort` variable, shared across all occurrences.
        let class_replace = obj.class_var.is_none().then(|| {
            let name = choose_fresh("V", vars);
            Term::var(vars.index_of(&name, obj.class_sort), obj.class_sort)
        });
        // The attribute-set variable: the pattern's own one, or a fresh `Atts:AttributeSet`.
        let atts_var = match &obj.pattern.set_var {
            Some(v) => Term::Var(v.clone()),
            None => {
                let name = choose_fresh("Atts", vars);
                Term::var(vars.index_of(&name, info.attr_set_sort), info.attr_set_sort)
            }
        };
        // Attributes present in a subject occurrence but absent from the pattern become fresh
        // kind-variable attributes in the pattern, using each attribute operator's domain kind.
        let pattern_syms: Vec<SymbolId> = obj.pattern.attrs.iter().map(|(s, _)| *s).collect();
        let mut added_attrs: Vec<(SymbolId, Term)> = Vec::new();
        for subj in &obj.subjects {
            for (sym, _) in &subj.attrs {
                if !pattern_syms.contains(sym) && !added_attrs.iter().any(|(s, _)| s == sym) {
                    let kind_sort = attribute_kind_sort(m, info, *sym);
                    let name = choose_fresh("A", vars);
                    let var = Term::var(vars.index_of(&name, kind_sort), kind_sort);
                    added_attrs.push((*sym, Term::op(*sym, vec![var])));
                }
            }
        }
        let mut pattern_attrs = obj.pattern.attrs.clone();
        pattern_attrs.extend(added_attrs.iter().cloned());
        plans.insert(
            obj.oid.clone(),
            ObjPlan {
                class_replace,
                atts_var,
                pattern_attrs,
                added_attrs,
            },
        );
    }

    // --- Transform (mutable walk; rewrite each object occurrence from its plan). ---
    transform(lhs, Mode::Pattern, &plans, info, m);
    if let Some(rhs) = rhs {
        transform(rhs, Mode::Subject, &plans, info, m);
    }
    for frag in cond.iter_mut() {
        transform_condition(frag, &plans, info, m);
    }
    true
}

/// Recursively collect object occurrences from `term` under `mode`.
fn gather(
    term: &Term,
    mode: Mode,
    info: &OoInfo,
    m: &BuiltModule,
    objs: &mut Vec<ObjInfo>,
    ignore: &mut bool,
) {
    if let Term::Op { symbol, args } = term {
        if *symbol == info.object_ctor && args.len() == 3 {
            record_object(args, mode, info, m, objs, ignore);
        }
        // Continue recursively because object arguments and other soup elements may contain objects.
        for a in args {
            gather(a, mode, info, m, objs, ignore);
        }
    }
}

/// Record one `< oid : class | atts >` occurrence, updating gathered state for new or repeated object
/// identities in pattern and subject positions.
fn record_object(
    args: &[Term],
    mode: Mode,
    info: &OoInfo,
    m: &BuiltModule,
    objs: &mut Vec<ObjInfo>,
    ignore: &mut bool,
) {
    let (oid, class, atts) = (&args[0], &args[1], &args[2]);
    let existing = objs.iter().position(|o| o.oid == *oid);
    match existing {
        None => match mode {
            Mode::Pattern => {
                // First occurrence, on the LHS — the defining (pattern) occurrence.
                let Some((class_sort, class_var)) = classify_class(class, info, m) else {
                    *ignore = true; // class argument is neither a class constant nor a class-sorted variable
                    return;
                };
                let Some(pattern) = decompose_attr_set(atts, info, m) else {
                    *ignore = true;
                    return;
                };
                objs.push(ObjInfo {
                    oid: oid.clone(),
                    class_sort,
                    class_var,
                    class_arg: class.clone(),
                    pattern,
                    subjects: Vec::new(),
                });
            }
            // First seen on a RHS/condition: a "new" object with no LHS occurrence — quietly ignored.
            Mode::Subject => {}
            // An object pattern inside a condition fragment pattern disables completion.
            Mode::CondPattern => *ignore = true,
        },
        Some(idx) => match mode {
            // A duplicate object name on the LHS disables completion.
            Mode::Pattern => *ignore = true,
            Mode::CondPattern => *ignore = true,
            // A subject occurrence with a different class argument (a class-changing statement)
            // disables completion. The pattern's class argument is a class constant or class-sorted
            // variable, so structural equality is exact.
            Mode::Subject if *class != objs[idx].class_arg => *ignore = true,
            Mode::Subject => match decompose_attr_set(atts, info, m) {
                Some(occ) => objs[idx].subjects.push(occ),
                None => *ignore = true,
            },
        },
    }
}

/// Gather a condition fragment, assigning pattern or subject mode to each of its terms.
fn gather_condition(
    frag: &ConditionFragment,
    info: &OoInfo,
    m: &BuiltModule,
    objs: &mut Vec<ObjInfo>,
    ignore: &mut bool,
) {
    match frag {
        ConditionFragment::Equality { lhs, rhs } => {
            gather(lhs, Mode::Subject, info, m, objs, ignore);
            gather(rhs, Mode::Subject, info, m, objs, ignore);
        }
        ConditionFragment::SortTest { term, .. } => {
            gather(term, Mode::Subject, info, m, objs, ignore)
        }
        ConditionFragment::Matching {
            pattern, subject, ..
        } => {
            gather(pattern, Mode::CondPattern, info, m, objs, ignore);
            gather(subject, Mode::Subject, info, m, objs, ignore);
        }
        ConditionFragment::Rewrite { lhs, pattern, .. } => {
            gather(lhs, Mode::Subject, info, m, objs, ignore);
            gather(pattern, Mode::CondPattern, info, m, objs, ignore);
        }
    }
}

/// Classify a class argument. Returns `(class_sort, class_var_index)` for a class-sorted variable
/// (`Some(index)`) or an arity-zero constructor whose range is a class sort (`None` index). Any other
/// term returns `None` and disables completion.
fn classify_class(class: &Term, info: &OoInfo, m: &BuiltModule) -> Option<(SortId, Option<u32>)> {
    match class {
        Term::Var(v) => info
            .class_sorts
            .contains(&v.sort)
            .then_some((v.sort, Some(v.index))),
        Term::Op { symbol, args } if args.is_empty() => {
            let range = m.engine.symbol_declarations(*symbol).first()?.1;
            info.class_sorts.contains(&range).then_some((range, None))
        }
        _ => None,
    }
}

/// Decompose an attribute-set term into its individual attribute terms, keyed by head operator, and at
/// most one attribute-set variable. A duplicate attribute, second set variable, variable of another
/// sort, or unrecognized subterm returns `None` and disables completion.
fn decompose_attr_set(term: &Term, info: &OoInfo, m: &BuiltModule) -> Option<Occ> {
    let mut occ = Occ {
        attrs: Vec::new(),
        set_var: None,
    };
    walk_attr_set(term, info, m, &mut occ).then_some(occ)
}

fn walk_attr_set(term: &Term, info: &OoInfo, m: &BuiltModule, occ: &mut Occ) -> bool {
    match term {
        // Nested `_,_` — recurse over the elements.
        Term::Op { symbol, args } if *symbol == info.attr_set_sym => {
            args.iter().all(|a| walk_attr_set(a, info, m, occ))
        }
        // The attribute-set identity `none` — the empty set; contributes nothing.
        Term::Op { symbol, args } if args.is_empty() && Some(*symbol) == info.none_sym => true,
        // A variable of the AttributeSet sort — the (single) set variable.
        Term::Var(v) if v.sort == info.attr_set_sort => {
            if occ.set_var.is_some() {
                return false; // two set variables — disable
            }
            occ.set_var = Some(v.clone());
            true
        }
        // An attribute term: its head must be an attribute operator (unary, ranging on a strict subsort
        // of AttributeSet, i.e. Attribute), keyed by head; a duplicate head disables completion.
        Term::Op { symbol, .. } if is_attribute_op(*symbol, info, m) => {
            if occ.attrs.iter().any(|(s, _)| s == symbol) {
                return false; // duplicate attribute — disable
            }
            occ.attrs.push((*symbol, term.clone()));
            true
        }
        // Anything else (a non-attribute operator such as an `Attribute` constant, a variable of the
        // wrong sort) is unrecognized.
        _ => false,
    }
}

/// Whether `sym` is an attribute operator: a unary operator whose result is a strict subsort of
/// `AttributeSet`. Only a unary head has the value position that completion fills with a fresh kind
/// variable (`a(A:[K])`) when it adds the attribute to the pattern, so an `Attribute` constant or a
/// non-unary operator is unrecognized.
fn is_attribute_op(sym: SymbolId, info: &OoInfo, m: &BuiltModule) -> bool {
    m.engine
        .symbol_declarations(sym)
        .first()
        .is_some_and(|(domain, range)| {
            domain.len() == 1
                && *range != info.attr_set_sort
                && m.engine.sorts().leq(*range, info.attr_set_sort)
        })
}

/// Require a pattern set variable to occur identically in every subject occurrence and nowhere else.
/// Without a pattern set variable, no subject may contain one. Failure disables completion.
fn check_variables(
    objs: &[ObjInfo],
    lhs: &Term,
    rhs: Option<&Term>,
    cond: &[ConditionFragment],
) -> bool {
    // Occurrence counts per variable index, across the whole statement.
    let mut counts: HashMap<u32, usize> = HashMap::new();
    count_vars(lhs, &mut counts);
    if let Some(rhs) = rhs {
        count_vars(rhs, &mut counts);
    }
    for frag in cond {
        for t in condition_terms(frag) {
            count_vars(t, &mut counts);
        }
    }
    for obj in objs {
        let occurrences = 1 + obj.subjects.len();
        // A class variable may appear only once as the class of each occurrence.
        if let Some(cv) = obj.class_var
            && counts.get(&cv).copied().unwrap_or(0) > occurrences
        {
            return false;
        }
        match &obj.pattern.set_var {
            None => {
                // No pattern set variable ⇒ no subject may carry one.
                if obj.subjects.iter().any(|s| s.set_var.is_some()) {
                    return false;
                }
            }
            Some(pv) => {
                // Every subject must carry the same set variable, used nowhere else.
                for s in &obj.subjects {
                    match &s.set_var {
                        Some(sv) if sv.index == pv.index => {}
                        _ => return false,
                    }
                }
                if counts.get(&pv.index).copied().unwrap_or(0) > occurrences {
                    return false;
                }
            }
        }
    }
    true
}

/// Rewrite each object occurrence in `term` under `mode` from its plan.
fn transform(
    term: &mut Term,
    mode: Mode,
    plans: &HashMap<Term, ObjPlan>,
    info: &OoInfo,
    m: &BuiltModule,
) {
    if let Term::Op { symbol, args } = term {
        if *symbol == info.object_ctor
            && args.len() == 3
            && let Some(plan) = plans.get(&args[0])
        {
            apply_object(args, mode, plan, info, m);
        }
        for a in args.iter_mut() {
            transform(a, mode, plans, info, m);
        }
    }
}

fn transform_condition(
    frag: &mut ConditionFragment,
    plans: &HashMap<Term, ObjPlan>,
    info: &OoInfo,
    m: &BuiltModule,
) {
    match frag {
        ConditionFragment::Equality { lhs, rhs } => {
            transform(lhs, Mode::Subject, plans, info, m);
            transform(rhs, Mode::Subject, plans, info, m);
        }
        ConditionFragment::SortTest { term, .. } => transform(term, Mode::Subject, plans, info, m),
        ConditionFragment::Matching {
            pattern, subject, ..
        } => {
            transform(pattern, Mode::CondPattern, plans, info, m);
            transform(subject, Mode::Subject, plans, info, m);
        }
        ConditionFragment::Rewrite { lhs, pattern, .. } => {
            transform(lhs, Mode::Subject, plans, info, m);
            transform(pattern, Mode::CondPattern, plans, info, m);
        }
    }
}

/// Apply one object's plan to a `< oid : class | atts >` argument vector (`args[1]` = class, `args[2]` =
/// attribute set), rebuilding the attribute set per `mode`.
fn apply_object(args: &mut [Term], mode: Mode, plan: &ObjPlan, info: &OoInfo, m: &BuiltModule) {
    if let Some(vt) = &plan.class_replace {
        args[1] = vt.clone();
    }
    // The occurrence's own attributes + set variable, then the shared attribute-set variable. (The set
    // was validated during gather, so this re-walk succeeds.)
    let mut own = Occ {
        attrs: Vec::new(),
        set_var: None,
    };
    let _ = walk_attr_set(&args[2], info, m, &mut own);
    let atts = own
        .set_var
        .as_ref()
        .map_or_else(|| plan.atts_var.clone(), |v| Term::Var(v.clone()));

    let mut elems: Vec<Term> = Vec::new();
    match mode {
        Mode::Pattern => {
            // Existing pattern attributes, followed by attributes introduced for subject-only keys.
            elems.extend(own.attrs.iter().map(|(_, t)| t.clone()));
            elems.extend(plan.added_attrs.iter().map(|(_, t)| t.clone()));
        }
        Mode::Subject | Mode::CondPattern => {
            // Pattern attributes this occurrence lacks (copied back), then its own attributes.
            for (sym, t) in &plan.pattern_attrs {
                if !own.attrs.iter().any(|(s, _)| s == sym) {
                    elems.push(t.clone());
                }
            }
            elems.extend(own.attrs.iter().map(|(_, t)| t.clone()));
        }
    }
    args[2] = if elems.is_empty() {
        atts
    } else {
        elems.push(atts);
        Term::op(info.attr_set_sym, elems)
    };
}

/// Return the kind sort of an attribute operator's argument. [`is_attribute_op`] admits only unary
/// operators, so the `AttributeSet`-kind fallback is defensive.
fn attribute_kind_sort(m: &BuiltModule, info: &OoInfo, attr_sym: SymbolId) -> SortId {
    let sorts = m.engine.sorts();
    let dom = m
        .engine
        .symbol_declarations(attr_sym)
        .into_iter()
        .find_map(|(d, _)| d.first().copied());
    sorts.error_sort(sorts.kind_of(dom.unwrap_or(info.attr_set_sort)))
}

/// Count occurrences of each variable index in `term`.
fn count_vars(term: &Term, counts: &mut HashMap<u32, usize>) {
    match term {
        Term::Var(v) => *counts.entry(v.index).or_insert(0) += 1,
        Term::Op { args, .. } => args.iter().for_each(|a| count_vars(a, counts)),
        Term::Na { .. } => {}
        Term::Iter { arg, .. } => count_vars(arg, counts),
    }
}

/// The terms carried by a condition fragment (for variable counting).
fn condition_terms(frag: &ConditionFragment) -> Vec<&Term> {
    match frag {
        ConditionFragment::Equality { lhs, rhs } => vec![lhs, rhs],
        ConditionFragment::SortTest { term, .. } => vec![term],
        ConditionFragment::Matching {
            pattern, subject, ..
        } => vec![pattern, subject],
        ConditionFragment::Rewrite { lhs, pattern, .. } => vec![lhs, pattern],
    }
}

/// Choose a variable name whose base no statement variable uses: `base`, then `base2`, `base3`, and so on.
/// A `VarIndex` name is the whole source token (`V:C` for an on-the-fly variable or a flattened declared
/// one), while printing and reflection identify a variable by its base name and sort, so each entry is
/// compared by the base before its first `:`.
fn choose_fresh(base: &str, vars: &VarIndex) -> String {
    let used = |name: &str| {
        (0..vars.count()).any(|i| {
            let source = vars.name(i);
            source
                .split_once(':')
                .map_or(source, |(source_base, _)| source_base)
                == name
        })
    };
    if !used(base) {
        return base.to_string();
    }
    let mut k = 2u64;
    loop {
        let name = format!("{base}{k}");
        if !used(&name) {
            return name;
        }
        k += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tnk_core::sort::Sorts;

    /// A fresh name avoids the base name of every statement variable: a bare declared name, an on-the-fly
    /// `V:C`, a flattened declared variable spelled `A:Oid`, and a fresh name chosen earlier.
    #[test]
    fn choose_fresh_avoids_statement_base_names() {
        let mut sorts = Sorts::new();
        let class = sorts.add_sort("C");
        let oid = sorts.add_sort("Oid");
        let mut vars = VarIndex::new();
        vars.index_of("O", oid);
        vars.index_of("V:C", class);
        vars.index_of("A:Oid", oid);
        assert_eq!(choose_fresh("O", &vars), "O2");
        assert_eq!(choose_fresh("V", &vars), "V2");
        assert_eq!(choose_fresh("A", &vars), "A2");
        assert_eq!(choose_fresh("Atts", &vars), "Atts");
        vars.index_of("V2", class);
        vars.index_of("V3:C", class);
        assert_eq!(choose_fresh("V", &vars), "V4");
    }
}
