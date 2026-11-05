//! The theory-matching seam: a compiled [`LhsAutomaton`] whose deterministic first phase returns a
//! resumable, multi-solution [`Subproblem`].
//!
//! The closed automaton set covers free patterns, free skeletons with theory-rooted aliens, ACU, AU,
//! CUI, and iterated successors. Multi-solution theory matches and heterogeneous alien compositions
//! share the same `next()` stream, so a failed condition can backtrack into the next match without
//! special-casing the reduction driver. The all-free path remains a direct structural match.
//!
//! [`LhsAutomaton::match_`] and [`Subproblem::next`] take the immutable `Signature` and mutable `Runtime`
//! separately. Conditions can reduce and theory matchers can allocate residue nodes while the statement
//! table remains borrowed.

use crate::acu::{AcuLhs, AcuSubproblem};
use crate::au::{AuLhs, AuSubproblem};
use crate::cui::{CuiLhs, CuiResidue, CuiSubproblem};
use crate::dag::{DagId, NodeTerm};
use crate::engine::{Runtime, Signature};
use crate::num::Nat;
use crate::s::{SLhs, SSubproblem};
use crate::symbol::{SymbolId, Theory};
use crate::term::{Subst, Term};
use std::collections::HashSet;
/// The theory residue of one rule-style match, detached from its resumable matcher. Conditional
/// strategy application solves conditions after releasing the match stream, then uses this snapshot to
/// splice the fully-instantiated right-hand side back into the unmatched subject portion.
#[derive(Clone)]
pub struct RewriteMatchContext {
    kind: RewriteMatchContextKind,
}

#[derive(Clone)]
enum RewriteMatchContextKind {
    Whole,
    Acu {
        symbol: SymbolId,
        residue: Vec<(DagId, u32)>,
    },
    Au {
        symbol: SymbolId,
        prefix: Vec<DagId>,
        suffix: Vec<DagId>,
    },
    Cui {
        symbol: SymbolId,
        residue: CuiResidue,
    },
    S {
        symbol: SymbolId,
        residue: Nat,
    },
}

impl RewriteMatchContext {
    pub(crate) fn whole() -> Self {
        Self {
            kind: RewriteMatchContextKind::Whole,
        }
    }

    pub(crate) fn acu(symbol: SymbolId, residue: Vec<(DagId, u32)>) -> Self {
        Self {
            kind: RewriteMatchContextKind::Acu { symbol, residue },
        }
    }

    pub(crate) fn au(symbol: SymbolId, prefix: Vec<DagId>, suffix: Vec<DagId>) -> Self {
        Self {
            kind: RewriteMatchContextKind::Au {
                symbol,
                prefix,
                suffix,
            },
        }
    }

    pub(crate) fn cui(symbol: SymbolId, residue: CuiResidue) -> Self {
        Self {
            kind: RewriteMatchContextKind::Cui { symbol, residue },
        }
    }

    pub(crate) fn successor(symbol: SymbolId, residue: Nat) -> Self {
        Self {
            kind: RewriteMatchContextKind::S { symbol, residue },
        }
    }

    pub(crate) fn build_result(
        &self,
        runtime: &mut Runtime,
        signature: &Signature,
        rhs: DagId,
    ) -> DagId {
        match &self.kind {
            RewriteMatchContextKind::Whole => rhs,
            RewriteMatchContextKind::Acu { symbol, residue } => {
                let mut parts = Vec::with_capacity(residue.len() + 1);
                parts.push((rhs, 1));
                parts.extend_from_slice(residue);
                runtime.make_acu(signature, *symbol, parts)
            }
            RewriteMatchContextKind::Au {
                symbol,
                prefix,
                suffix,
            } => {
                let mut sequence = Vec::with_capacity(prefix.len() + 1 + suffix.len());
                sequence.extend_from_slice(prefix);
                sequence.push(rhs);
                sequence.extend_from_slice(suffix);
                runtime.make_au(signature, *symbol, sequence)
            }
            RewriteMatchContextKind::Cui { symbol, residue } => {
                residue.rebuild(runtime, signature, *symbol, rhs)
            }
            RewriteMatchContextKind::S { symbol, residue } => {
                runtime.make_s(signature, *symbol, residue.clone(), rhs)
            }
        }
    }
}

/// A left-hand side compiled for matching in its theory. The enum is closed so dispatch stays static;
/// each variant owns the compiled representation its matching algorithm needs.
#[derive(Clone)]
pub(crate) enum LhsAutomaton {
    /// Free theory with an all-free pattern: direct structural matching with one deterministic solution.
    /// This is the hot path used by ordinary equations and prelude definitions.
    Free(Term),
    /// Free root containing theory-rooted child patterns. The free skeleton matches deterministically,
    /// then a [`Subproblem::Sequence`] composes the child matchers.
    FreeWithAliens(Term),
    /// ACU theory (`assoc comm [id:]`): multiset matching, genuinely multi-solution.
    Acu(AcuLhs),
    /// AU theory (`assoc [id:]`, not commutative): ordered-sequence matching with extension.
    Au(AuLhs),
    /// CUI theory (`comm [idem] [id:]`, not associative): commutative binary matching.
    Cui(CuiLhs),
    /// S theory (`iter`): unary stacked-successor matching with extension (`s^k` matches `s^n`).
    S(SLhs),
}

impl LhsAutomaton {
    /// Compile a pattern with no enclosing condition-variable conflicts.
    pub(crate) fn compile(lhs: Term, sig: &Signature) -> Self {
        Self::compile_avoiding_nonlinear_vars(lhs, sig, &HashSet::new())
    }

    /// Compile a statement pattern while preventing ACU's sole repeated-variable special case for
    /// variables used by the statement condition. All other theories ignore `condition_variables`.
    pub(crate) fn compile_avoiding_nonlinear_vars(
        lhs: Term,
        sig: &Signature,
        condition_variables: &HashSet<u32>,
    ) -> Self {
        match lhs.top_symbol().map(|s| sig.symbol(s).theory()) {
            Some(Theory::Acu) => LhsAutomaton::Acu(AcuLhs::compile_avoiding_nonlinear_vars(
                lhs,
                sig,
                condition_variables,
            )),
            Some(Theory::Au) => LhsAutomaton::Au(AuLhs::compile(lhs, sig)),
            Some(Theory::Cui) => LhsAutomaton::Cui(CuiLhs::compile(lhs, sig)),
            Some(Theory::S) => LhsAutomaton::S(SLhs::compile(lhs, sig)),
            // Keep theory-rooted children on the composed path so the common all-free case remains a
            // single deterministic match.
            _ if lhs.is_free_matchable(sig) => LhsAutomaton::Free(lhs),
            _ => LhsAutomaton::FreeWithAliens(lhs),
        }
    }

    /// First (deterministic) match phase: bind the forced part of the match into `subst` and return a
    /// residual [`Subproblem`] enumerating the solutions, or `None` if the subject cannot match at
    /// all. For the free theory the match is fully determined here, so the returned subproblem yields
    /// exactly the one solution already bound in `subst`.
    ///
    /// `ext_allowed` enables matching a sub-multiset or subsequence while retaining the unmatched residue.
    /// The free theory ignores it; ACU/AU use it for top-level rewriting and `xmatch`.
    ///
    /// `command` distinguishes interactive matching from rewrite/search. It enables command-only AU
    /// partition ordering, minimum matched spans, and subject-driven bare-variable extension.
    pub(crate) fn match_(
        &self,
        rt: &Runtime,
        sig: &Signature,
        subject: DagId,
        subst: &mut Subst,
        ext_allowed: bool,
        command: bool,
    ) -> Option<Subproblem> {
        match self {
            LhsAutomaton::Free(pat) => {
                // A bare variable in an extension command can match a sub-part selected by the
                // subject theory. S and AU expose matched portions; other theories fall back to a
                // whole-subject match with no `Matched portion` record.
                if command
                    && ext_allowed
                    && let Term::Var(v) = pat
                {
                    match &rt.node(subject).term {
                        NodeTerm::S { symbol, count, arg } => {
                            return Some(Subproblem::S(
                                SSubproblem::match_variable_with_extension(
                                    *symbol,
                                    count.clone(),
                                    *arg,
                                    v.index,
                                    v.sort,
                                ),
                            ));
                        }
                        NodeTerm::Au { symbol, args } => {
                            let identity = sig.symbol(*symbol).identity();
                            return Some(Subproblem::Au(
                                AuSubproblem::match_variable_with_extension(
                                    rt,
                                    sig,
                                    args.clone(),
                                    *symbol,
                                    identity,
                                    v.index,
                                    v.sort,
                                ),
                            ));
                        }
                        _ => {}
                    }
                }
                rt.match_pattern(sig, pat, subject, subst)
                    .then_some(Subproblem::FreeOnce { pending: true })
            }
            LhsAutomaton::FreeWithAliens(pat) => {
                // Bind the free skeleton and compose the theory-rooted child matchers.
                let mut aliens = Vec::new();
                rt.match_skeleton(sig, pat, subject, subst, &mut aliens)
                    .then(|| Subproblem::Sequence(SequenceSubproblem::new(aliens)))
            }
            LhsAutomaton::Acu(lhs) => lhs
                .match_(rt, sig, subject, ext_allowed)
                .map(Subproblem::Acu),
            LhsAutomaton::Au(lhs) => lhs
                .match_(rt, sig, subject, ext_allowed, command)
                .map(Subproblem::Au),
            LhsAutomaton::Cui(lhs) => lhs
                .match_(rt, sig, subject, ext_allowed)
                .map(Subproblem::Cui),
            // S reads only the runtime (the count comparison) — no `sig`/`subst` in its first phase.
            LhsAutomaton::S(lhs) => lhs.match_(rt, subject, ext_allowed).map(Subproblem::S),
        }
    }
}

/// A residual matching subproblem: a resumable enumerator of the remaining solutions of an
/// [`LhsAutomaton`] against a subject. [`Subproblem::next`] binds one solution into the shared `Subst`
/// and returns `true`, then returns `false` when exhausted. Associative and commutative matchers can
/// contribute several solutions; condition failure resumes the same stream. Sequence and disjunction
/// variants compose heterogeneous sub-matches without dynamic dispatch.
// Matching is a hot path; keeping the resumable state inline avoids one allocation per match.
#[allow(clippy::large_enum_variant)]
pub(crate) enum Subproblem {
    /// The free theory has at most one solution (a deterministic structural match), already bound in
    /// `subst` by [`LhsAutomaton::match_`]; `pending` yields it exactly once.
    FreeOnce { pending: bool },
    /// ACU theory: a resumable multiset-distribution enumerator (see [`AcuSubproblem`]).
    Acu(AcuSubproblem),
    /// AU theory: a resumable ordered-sequence enumerator (see [`AuSubproblem`]).
    Au(AuSubproblem),
    /// CUI theory: the commutative, collapse, and collapse-extension pairings (see [`CuiSubproblem`]).
    Cui(CuiSubproblem),
    /// S theory: the (lazy) successor-extension solutions (see [`SSubproblem`]).
    S(SSubproblem),
    /// Recursively composed theory-rooted children of a free-rooted pattern.
    Sequence(SequenceSubproblem),
}

impl Subproblem {
    /// Advance to the next solution, binding it into `subst`; `false` when exhausted. Multi-solution
    /// ACU/AU arms need `&mut Runtime` to build binding and residue nodes between solutions. The free arm
    /// ignores `rt`/`sig`/`subst` because its single solution was bound during `match_`.
    pub(crate) fn next(&mut self, rt: &mut Runtime, sig: &Signature, subst: &mut Subst) -> bool {
        match self {
            // Yield the already-bound solution exactly once.
            Subproblem::FreeOnce { pending } => core::mem::replace(pending, false),
            Subproblem::Acu(sp) => sp.next(rt, sig, subst),
            Subproblem::Au(sp) => sp.next(rt, sig, subst),
            Subproblem::Cui(sp) => sp.next(rt, sig, subst),
            Subproblem::S(sp) => sp.next(rt, sig, subst),
            Subproblem::Sequence(sp) => sp.next(rt, sig, subst),
        }
    }
    pub(crate) fn rewrite_context(&self) -> RewriteMatchContext {
        match self {
            Subproblem::FreeOnce { .. } | Subproblem::Sequence(_) => RewriteMatchContext::whole(),
            Subproblem::Acu(subproblem) => subproblem.rewrite_context(),
            Subproblem::Au(subproblem) => subproblem.rewrite_context(),
            Subproblem::Cui(subproblem) => subproblem.rewrite_context(),
            Subproblem::S(subproblem) => subproblem.rewrite_context(),
        }
    }

    /// Extension-match status of the current solution for `xmatch` display. `None` suppresses the
    /// `Matched portion` line, `Some(true)` means the whole subject, and `Some(false)` means a genuine
    /// sub-portion that the caller rebuilds from the instantiated pattern.
    pub(crate) fn matched_status(&self) -> Option<bool> {
        match self {
            Subproblem::FreeOnce { .. } | Subproblem::Sequence(_) => None,
            Subproblem::Acu(sp) => sp.matched_status(),
            Subproblem::Au(sp) => sp.matched_status(),
            // CUI extension display has no matched-portion form.
            Subproblem::Cui(_) => None,
            Subproblem::S(sp) => sp.matched_status(),
        }
    }

    pub(crate) fn ordered_context_parts(&self) -> Option<(&[DagId], &[DagId])> {
        match self {
            Subproblem::Au(subproblem) => Some(subproblem.ordered_context_parts()),
            _ => None,
        }
    }

    /// Build the rewrite result by splicing the instantiated `rhs` into the matched position: a whole
    /// match (the free theory, or an extension match with no residue) is just `rhs`; an extension
    /// match reassembles residue in theory-normal form: an ACU multiset or AU prefix/suffix.
    pub(crate) fn build_result(&self, rt: &mut Runtime, sig: &Signature, rhs: DagId) -> DagId {
        match self {
            Subproblem::FreeOnce { .. } => rhs,
            Subproblem::Acu(sp) => sp.build_result(rt, sig, rhs),
            Subproblem::Au(sp) => sp.build_result(rt, sig, rhs),
            Subproblem::Cui(sp) => sp.build_result(rt, sig, rhs),
            Subproblem::S(sp) => sp.build_result(rt, sig, rhs),
            // A free-rooted match consumes the whole subject (no extension), so the result is just rhs.
            Subproblem::Sequence(_) => rhs,
        }
    }
}

/// Recursively compose the theory-rooted child patterns collected from a free skeleton. All child
/// automata share one substitution, and their combinations are replayed through nested backtracking.
pub(crate) struct SequenceSubproblem {
    aliens: Vec<(Term, DagId)>,
    /// The alien sub-patterns' variable indices, captured into each recorded solution.
    alien_var_indices: Vec<u32>,
    /// Fully-built solutions (each a variable-binding snapshot); `None` until the first `next`.
    recorded: Option<Vec<Vec<(u32, DagId)>>>,
    rec_cursor: usize,
    bound: Vec<u32>,
}

impl SequenceSubproblem {
    fn new(aliens: Vec<(Term, DagId)>) -> Self {
        let mut alien_var_indices = Vec::new();
        for (t, _) in &aliens {
            collect_vars(t, &mut alien_var_indices);
        }
        SequenceSubproblem {
            aliens,
            alien_var_indices,
            recorded: None,
            rec_cursor: 0,
            bound: Vec::new(),
        }
    }

    fn next(&mut self, rt: &mut Runtime, sig: &Signature, subst: &mut Subst) -> bool {
        for &idx in &self.bound {
            subst.unbind(idx);
        }
        self.bound.clear();
        if self.recorded.is_none() {
            let sols = self.enumerate(rt, sig, subst);
            self.recorded = Some(sols);
        }
        let binds = {
            let recorded = self.recorded.as_ref().expect("just enumerated");
            if self.rec_cursor >= recorded.len() {
                return false;
            }
            recorded[self.rec_cursor].clone()
        };
        self.rec_cursor += 1;
        for &(idx, b) in &binds {
            subst.bind(idx, b);
            self.bound.push(idx);
        }
        true
    }

    /// Enumerate every combination of the aliens' solutions (nested backtracking, shared scratch seeded
    /// from `base` so the free skeleton's variable bindings are respected).
    fn enumerate(&self, rt: &mut Runtime, sig: &Signature, base: &Subst) -> Vec<Vec<(u32, DagId)>> {
        enumerate_alien_solutions(rt, sig, base, &self.aliens, &self.alien_var_indices)
    }
}

/// Match each `(pattern, subject)` alien pair recursively, composing the solutions by nested
/// backtracking over a shared scratch substitution (seeded from `base`), and return each combined
/// solution as a snapshot of `var_indices`. The general cross-theory sub-matching primitive: it drives
/// each sub-pattern through the full [`LhsAutomaton`] seam, so an alien may be free, theory-rooted, or
/// mixed — and nested aliens compose recursively. Shared by the free [`SequenceSubproblem`] and by the
/// S/CUI theory matchers, so all sub-pattern matching is uniformly cross-theory (no `match_pattern`
/// "free only" islands). Eager (records full solutions, like the ACU/AU paths); the caller replays them.
pub(crate) fn enumerate_alien_solutions(
    rt: &mut Runtime,
    sig: &Signature,
    base: &Subst,
    aliens: &[(Term, DagId)],
    var_indices: &[u32],
) -> Vec<Vec<(u32, DagId)>> {
    let mut out = Vec::new();
    let mut scratch = base.clone();
    rec_aliens(0, aliens, var_indices, rt, sig, &mut scratch, &mut out);
    out
}

fn rec_aliens(
    idx: usize,
    aliens: &[(Term, DagId)],
    var_indices: &[u32],
    rt: &mut Runtime,
    sig: &Signature,
    scratch: &mut Subst,
    out: &mut Vec<Vec<(u32, DagId)>>,
) {
    if idx == aliens.len() {
        out.push(
            var_indices
                .iter()
                .filter_map(|&i| scratch.get(i).map(|b| (i, b)))
                .collect(),
        );
        return;
    }
    let (pat, subj) = &aliens[idx];
    let automaton = LhsAutomaton::compile(pat.clone(), sig);
    let checkpoint = scratch.clone();
    if let Some(mut sp) = automaton.match_(rt, sig, *subj, scratch, false, false) {
        while sp.next(rt, sig, scratch) {
            rec_aliens(idx + 1, aliens, var_indices, rt, sig, scratch, out);
        }
    }
    *scratch = checkpoint;
}

/// Collect the distinct variable indices in a pattern (an alien's internal bindings to capture).
fn collect_vars(t: &Term, out: &mut Vec<u32>) {
    match t {
        Term::Var(v) => {
            if !out.contains(&v.index) {
                out.push(v.index);
            }
        }
        Term::Na { .. } => {} // a literal introduces no variables
        Term::Op { args, .. } => args.iter().for_each(|a| collect_vars(a, out)),
        Term::Iter { arg, .. } => collect_vars(arg, out),
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::Engine;

    /// The free arm is single-solution: `match_` binds it, the subproblem yields it once, then stays
    /// exhausted across further `next` calls (the contract the reduce driver relies on).
    #[test]
    fn free_automaton_yields_exactly_one_solution() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let a = e.add_op("a", vec![], nat);
        let f = e.add_op("f", vec![nat, nat], nat);
        let a0 = e.make_const(a);
        let a1 = e.make_const(a);
        let subject = e.make_free(f, vec![a0, a1]); // f(a, a)

        let lhs = LhsAutomaton::compile(
            Term::op(f, vec![Term::var(0, nat), Term::constant(a)]),
            e.signature(),
        ); // f(X, a)
        let mut subst = Subst::new();
        subst.reset(1);
        let (sig, rt) = e.parts_mut();
        let mut sp = lhs
            .match_(rt, sig, subject, &mut subst, false, false)
            .expect("f(a,a) matches f(X,a)");
        assert!(sp.next(rt, sig, &mut subst), "the one solution");
        assert_eq!(subst.get(0), Some(a0), "X bound to the first argument");
        assert!(
            !sp.next(rt, sig, &mut subst),
            "free theory has a single solution"
        );
        assert!(
            !sp.next(rt, sig, &mut subst),
            "an exhausted subproblem stays exhausted"
        );
    }

    /// A non-matching subject yields `None` from `match_` (no subproblem to drive).
    #[test]
    fn free_automaton_reports_non_match() {
        let mut e = Engine::new();
        let nat = e.add_sort("Nat");
        e.close_sorts();
        let a = e.add_op("a", vec![], nat);
        let b = e.add_op("b", vec![], nat);
        let f = e.add_op("f", vec![nat, nat], nat);
        let b0 = e.make_const(b);
        let b1 = e.make_const(b);
        let subject = e.make_free(f, vec![b0, b1]); // f(b, b)

        let lhs = LhsAutomaton::compile(
            Term::op(f, vec![Term::var(0, nat), Term::constant(a)]),
            e.signature(),
        ); // f(X, a)
        let mut subst = Subst::new();
        subst.reset(1);
        assert!(
            lhs.match_(
                e.runtime(),
                e.signature(),
                subject,
                &mut subst,
                false,
                false
            )
            .is_none(),
            "f(b,b) does not match f(X,a)"
        );
    }
}
