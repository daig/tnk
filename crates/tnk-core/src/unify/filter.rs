//! The irredundant-unification filter keeps a minimal set of unifiers that are most general on the
//! input variables, discarding any unifier that is an instance of a retained one.
//!
//! A retained unifier `r` subsumes candidate `u` iff `u` is an instance of `r` on those variables.
//! When matching cannot represent the equation theory, satisfiability of
//! `{ r[i] =? freeze(u[i]) }` decides subsumption instead. `freeze` replaces `u`'s fresh variables
//! with distinct ground constants, leaving only the variables from `r`; [`UnifyProblem`] then covers
//! every implemented unification theory.

use crate::dag::{DagId, NodeTerm};
use crate::engine::Engine;
use crate::fresh::VariableFamily;
use crate::host::ReducerFault;
use crate::num::Nat;
use crate::sort::SortId;
use crate::symbol::SymbolId;
use crate::term::Term;

use super::problem::{UnifyProblem, VarSpec};
use super::{NameCodes, UnifyEnv, is_ground};

/// Return the most-general subset of `unifiers`, whose entries contain input-variable bindings in
/// slot order. A candidate subsumed by a survivor is dropped; otherwise it evicts every survivor it
/// subsumes and is appended. Survivor order therefore follows enumeration order.
pub fn irredundant(e: &mut Engine, unifiers: Vec<Vec<DagId>>) -> Vec<Vec<DagId>> {
    let mut survivors: Vec<Vec<DagId>> = Vec::new();
    'candidate: for u in unifiers {
        for r in &survivors {
            if subsumes(e, r, &u) {
                continue 'candidate; // u is an instance of a retained unifier — redundant
            }
        }
        // u survives: evict every retained unifier that is an instance of u, then append u.
        let mut kept: Vec<Vec<DagId>> = Vec::with_capacity(survivors.len() + 1);
        for r in survivors.drain(..) {
            if !subsumes(e, &u, &r) {
                kept.push(r);
            }
        }
        kept.push(u);
        survivors = kept;
    }
    survivors
}

/// Fallible form of [`irredundant`].
pub fn try_irredundant(
    e: &mut Engine,
    unifiers: Vec<Vec<DagId>>,
) -> Result<Vec<Vec<DagId>>, ReducerFault> {
    let result = irredundant(e, unifiers);
    e.check_deferred_reducer_fault()?;
    Ok(result)
}

/// A throwaway name-code source for the subsumption sub-problem: satisfiability does not depend on
/// the fresh variables' names (only whether *some* order-sorted unifier exists), so any injective
/// coding suffices.
#[derive(Default)]
struct ScratchNames {
    next: u32,
}
impl NameCodes for ScratchNames {
    fn code(&mut self, _name: &str) -> u32 {
        let c = self.next;
        self.next += 1;
        c
    }
}

/// Whether `candidate` is an instance of `retained` modulo the equation theory. Both slices contain
/// one binding per input variable in slot order.
pub(crate) fn subsumes(e: &mut Engine, retained: &[DagId], candidate: &[DagId]) -> bool {
    // Matching is cheaper when it supports every theory in the vectors. One-sided identity is the
    // sole matcher gap, so only those vectors need the frozen-unification fallback.
    if !retained
        .iter()
        .chain(candidate)
        .copied()
        .any(|dag| contains_one_sided_identity(e, dag))
    {
        let mut variables = Vec::new();
        let patterns: Vec<Term> = retained
            .iter()
            .map(|&dag| dag_to_matching_term(e, dag, &mut variables))
            .collect();
        return e.shared_match_exists(patterns, candidate, variables.len() as u32);
    }
    // Re-slot `retained`'s variables to contiguous indices `0..m`, collecting their specs — these are
    // the only variables of the sub-problem. A fresh variable shared across bindings keeps one slot.
    let mut reslot: Vec<((u32, SortId), u32)> = Vec::new();
    let mut specs: Vec<VarSpec> = Vec::new();
    let lhs: Vec<DagId> = retained
        .iter()
        .map(|&d| reindex(e, d, &mut reslot, &mut specs))
        .collect();

    // Freeze `candidate`'s variables to fresh distinct ground constants (one per distinct variable),
    // leaving no variables on the subject side.
    let mut frozen_map: Vec<((u32, SortId), DagId)> = Vec::new();
    let rhs: Vec<DagId> = candidate
        .iter()
        .map(|&d| freeze(e, d, &mut frozen_map))
        .collect();

    let equations: Vec<(DagId, DagId)> = lhs.into_iter().zip(rhs).collect();
    let mut names = ScratchNames::default();
    let mut env = UnifyEnv {
        e,
        names: &mut names,
    };
    let mut prob = UnifyProblem::new(&mut env, equations, specs, VariableFamily::Unify, "0");
    prob.find_next_deferred(&mut env).is_some()
}

fn contains_one_sided_identity(e: &Engine, root: DagId) -> bool {
    let mut work = vec![root];
    while let Some(dag) = work.pop() {
        let node = e.node(dag);
        let symbol = e.symbol(node.symbol());
        if symbol.identity().is_none()
            && (symbol.left_identity().is_some() || symbol.right_identity().is_some())
        {
            return true;
        }
        work.extend(node.children());
    }
    false
}

fn dag_to_matching_term(e: &Engine, dag: DagId, variables: &mut Vec<(u32, SortId)>) -> Term {
    match &e.node(dag).term {
        NodeTerm::Var { name, .. } => {
            let key = (*name, e.sort_of(dag));
            let slot = match variables.iter().position(|&candidate| candidate == key) {
                Some(slot) => slot,
                None => {
                    variables.push(key);
                    variables.len() - 1
                }
            };
            Term::var(slot as u32, key.1)
        }
        NodeTerm::Free { symbol, args }
        | NodeTerm::Au { symbol, args }
        | NodeTerm::Cui { symbol, args } => Term::op(
            *symbol,
            args.iter()
                .map(|&child| dag_to_matching_term(e, child, variables))
                .collect(),
        ),
        NodeTerm::Acu { symbol, args } => Term::op(
            *symbol,
            args.iter()
                .flat_map(|&(child, multiplicity)| {
                    std::iter::repeat_n(child, multiplicity as usize)
                })
                .map(|child| dag_to_matching_term(e, child, variables))
                .collect(),
        ),
        NodeTerm::S { symbol, count, arg } => Term::iter(
            *symbol,
            count.clone(),
            dag_to_matching_term(e, *arg, variables),
        ),
        NodeTerm::Na { symbol, value } => Term::Na {
            symbol: *symbol,
            value: value.clone(),
        },
    }
}

/// Rebuild `dag`, replacing each variable leaf with `make_var` at a contiguous slot (assigned in
/// first-encounter order via `reslot`, shared across a retained unifier's bindings) and recording its
/// [`VarSpec`]. Ground structure is returned unchanged.
fn reindex(
    e: &mut Engine,
    dag: DagId,
    reslot: &mut Vec<((u32, SortId), u32)>,
    specs: &mut Vec<VarSpec>,
) -> DagId {
    rebuild(e, dag, &mut |e, name, sort| {
        let key = (name, sort);
        let slot = match reslot.iter().find(|(k, _)| *k == key) {
            Some((_, s)) => *s,
            None => {
                let s = reslot.len() as u32;
                reslot.push((key, s));
                specs.push(VarSpec { sort, name });
                s
            }
        };
        e.make_var(sort, name, slot)
    })
}

/// Rebuild `dag`, replacing each variable leaf with a fresh ground constant of its sort (one per
/// distinct variable, cached in `frozen_map`). Ground structure is returned unchanged.
fn freeze(e: &mut Engine, dag: DagId, frozen_map: &mut Vec<((u32, SortId), DagId)>) -> DagId {
    rebuild(e, dag, &mut |e, name, sort| {
        let key = (name, sort);
        match frozen_map.iter().find(|(k, _)| *k == key) {
            Some((_, c)) => *c,
            None => {
                let c = e.fresh_constant(sort);
                frozen_map.push((key, c));
                c
            }
        }
    })
}

/// Deep-rebuild `dag`, mapping each variable leaf through `leaf(engine, name_code, sort)` and copying
/// every other node verbatim (associative multiplicities preserved, `s^n` re-nested). A ground
/// subterm is shared unchanged — it contains no variables to remap.
fn rebuild(
    e: &mut Engine,
    dag: DagId,
    leaf: &mut dyn FnMut(&mut Engine, u32, SortId) -> DagId,
) -> DagId {
    if is_ground(e, dag) {
        return dag;
    }
    // Snapshot the node under the immutable borrow, then rebuild (which needs `&mut Engine`).
    enum Shape {
        Var(u32, SortId),
        Free(SymbolId, Vec<DagId>),
        Acu(SymbolId, Vec<(DagId, u32)>),
        Au(SymbolId, Vec<DagId>),
        Cui(SymbolId, DagId, DagId),
        S(SymbolId, Nat, DagId),
    }
    let shape = match &e.node(dag).term {
        NodeTerm::Var { name, .. } => Shape::Var(*name, e.sort_of(dag)),
        NodeTerm::Free { symbol, args } => Shape::Free(*symbol, args.clone()),
        NodeTerm::Acu { symbol, args } => Shape::Acu(*symbol, args.clone()),
        NodeTerm::Au { symbol, args } => Shape::Au(*symbol, args.clone()),
        NodeTerm::Cui { symbol, args } => Shape::Cui(*symbol, args[0], args[1]),
        NodeTerm::S { symbol, count, arg } => Shape::S(*symbol, count.clone(), *arg),
        // `is_ground` already returned for a literal (no variables); unreachable here.
        NodeTerm::Na { .. } => return dag,
    };
    match shape {
        Shape::Var(name, sort) => leaf(e, name, sort),
        Shape::Free(sym, args) => {
            let a = args.into_iter().map(|c| rebuild(e, c, leaf)).collect();
            e.make_free(sym, a)
        }
        Shape::Acu(sym, pairs) => {
            let p = pairs
                .into_iter()
                .map(|(c, m)| (rebuild(e, c, leaf), m))
                .collect();
            e.make_acu(sym, p)
        }
        Shape::Au(sym, els) => {
            let a = els.into_iter().map(|c| rebuild(e, c, leaf)).collect();
            e.make_au(sym, a)
        }
        Shape::Cui(sym, x, y) => {
            let nx = rebuild(e, x, leaf);
            let ny = rebuild(e, y, leaf);
            e.make_cui(sym, nx, ny)
        }
        Shape::S(sym, count, arg) => {
            // Keep the arbitrary-precision count: a binding's count may exceed a machine word.
            let narg = rebuild(e, arg, leaf);
            let (sig, rt) = e.parts_mut();
            rt.make_s(sig, sym, count, narg)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `X --> #1` (a fresh variable) is strictly more general than `X --> 0` (a constant): the
    /// variable binding subsumes the constant one, not vice versa. Exercises `subsumes` in both
    /// directions through the reindex/freeze/satisfiability path.
    #[test]
    fn variable_binding_subsumes_constant_binding() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);

        let general = vec![e.make_var(nat, 1, 0)]; // X --> #1:Nat
        let instance = vec![e.make_const(zero)]; //   X --> 0

        assert!(subsumes(&mut e, &general, &instance), "#1 subsumes 0");
        assert!(
            !subsumes(&mut e, &instance, &general),
            "0 does not subsume #1"
        );
    }

    /// The filter keeps only the most-general unifier, in enumeration order, whichever order the
    /// redundant and general unifiers arrive in (drop-if-subsumed vs evict-then-append).
    #[test]
    fn irredundant_keeps_the_general_unifier() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let zero = e.add_op("0", vec![], nat);

        // General first: the instance that follows is dropped as redundant.
        let general = vec![e.make_var(nat, 1, 0)];
        let instance = vec![e.make_const(zero)];
        let kept = irredundant(&mut e, vec![general, instance]);
        assert_eq!(kept.len(), 1);
        assert!(matches!(e.node(kept[0][0]).term, NodeTerm::Var { .. }));

        // Instance first: the general unifier that follows evicts it.
        let general = vec![e.make_var(nat, 1, 0)];
        let instance = vec![e.make_const(zero)];
        let kept = irredundant(&mut e, vec![instance, general]);
        assert_eq!(kept.len(), 1);
        assert!(matches!(e.node(kept[0][0]).term, NodeTerm::Var { .. }));
    }

    /// A one-sided identity sends `subsumes` through the frozen-unification fallback, which rebuilds
    /// each binding. An `iter` count beyond `u64` must survive that rebuild in both directions.
    #[test]
    fn one_sided_identity_fallback_keeps_bignum_iter_counts() {
        use crate::symbol::IdentitySide;
        let mut e = Engine::new();
        let n = e.add_sort("N");
        e.close_sorts();
        let z = e.add_op("z", vec![], n);
        let a = e.add_op("a", vec![], n);
        let s = e.add_op_iter("s_", vec![n], n);
        let g = e.add_op("g", vec![n, n], n);
        e.reserve_one_sided_identity(g, IdentitySide::Left, n);
        e.set_one_sided_identity_term(g, Term::constant(z));
        let count = "18446744073709551619"; // 2^64 + 3

        // General: X --> s^count(g(#1, #2)); instance: X --> s^count(g(#3, a)).
        let (v1, v2, v3) = (
            e.make_var(n, 1, 0),
            e.make_var(n, 2, 1),
            e.make_var(n, 3, 2),
        );
        let inner = e.make_free(g, vec![v1, v2]);
        let general = vec![e.make_iter_decimal(s, count, inner).unwrap()];
        let ac = e.make_const(a);
        let inner = e.make_free(g, vec![v3, ac]);
        let instance = vec![e.make_iter_decimal(s, count, inner).unwrap()];

        assert!(
            subsumes(&mut e, &general, &instance),
            "general subsumes instance"
        );
        assert!(
            !subsumes(&mut e, &instance, &general),
            "instance does not subsume general"
        );
    }
}
