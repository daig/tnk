//! CUI matching: a matcher for `comm` (commutative, **not** associative; optionally `idem`/`id:`)
//! binary operators.
//!
//! A CUI node is binary. Matching `f(p1, p2)` against canonical `f(s1, s2)` enumerates both
//! commutative pairings. With `id:`, extension matching also lets one operand take the identity while
//! the other matches one subject argument; the remaining argument stays as rewrite residue in its own
//! position. Against any subject, `id:` and `idem` collapse arms match the operands against the
//! identity/whole subject; at an `f`-rooted subject they follow the whole-node pairings.
//!
//! Each argument sub-pattern is matched through the full [`LhsAutomaton`](crate::theory) seam (via
//! [`enumerate_alien_solutions`](crate::theory::enumerate_alien_solutions)), so it may be a variable
//! (including the non-linear `f(X, X)`), a ground/free subterm, or a theory-rooted subterm. Statement
//! indexing is separate from this matcher: each membership is compiled once, then referenced from either
//! its direct-symbol index or a result-kind collapse index. Runtime whole matching rejects conservative
//! collapse candidates that cannot apply to the current subject.

use crate::dag::{DagId, NodeTerm};
use crate::engine::{Runtime, Signature};
use crate::symbol::{IdentityId, SymbolId};
use crate::term::{Subst, Term};
use crate::theory::{RewriteMatchContext, enumerate_alien_solutions};

/// A compiled CUI left-hand side: the binary pattern `f(p1, p2)` plus the variable indices it binds.
#[derive(Clone)]
pub(crate) struct CuiLhs {
    symbol: SymbolId,
    p1: Term,
    p2: Term,
    var_indices: Vec<u32>,
}

impl CuiLhs {
    pub(crate) fn compile(lhs: Term, _sig: &Signature) -> Self {
        let symbol = lhs.top_symbol().expect("CUI lhs must be an application");
        let (p1, p2) = match lhs {
            Term::Op { args, .. } => {
                let mut args = args;
                assert_eq!(args.len(), 2, "a CUI pattern is binary");
                let p2 = args.pop().unwrap();
                let p1 = args.pop().unwrap();
                (p1, p2)
            }
            Term::Var(_) | Term::Iter { .. } | Term::Na { .. } => {
                unreachable!("compile is only called on a CUI application lhs")
            }
        };
        let mut var_indices = Vec::new();
        collect_vars(&p1, &mut var_indices);
        collect_vars(&p2, &mut var_indices);
        CuiLhs {
            symbol,
            p1,
            p2,
            var_indices,
        }
    }

    /// Match the binary pattern against a subject. Pairings are enumerated lazily in
    /// [`CuiSubproblem::next`] (each argument is matched through the full matcher seam, which needs
    /// `&mut Runtime` for a theory-rooted argument); this phase classifies the subject and builds the
    /// pairing list:
    /// - a CUI node of this operator: the whole-node pairings (both orders when `comm`), preceded —
    ///   when extension is allowed and the op has `id:` — by the **collapse-extension** pairings
    ///   (one pattern operand takes the identity, the other matches ONE argument, the remaining
    ///   argument is the residue and keeps its position: `eq a * X = c` on `a * b` gives `b * c`,
    ///   and on `b # a` for a non-commutative `#` gives `b # c`, with identity-first ordering),
    ///   and followed by the collapse arms below against the whole node (`f(X, Y) <=? f(a, b)`
    ///   with `id: e` also yields `X --> f(a, b), Y --> e` and `X --> e, Y --> f(a, b)`).
    /// - any subject, for an op with `id:`/`idem`: one operand matches the identity and the other
    ///   the whole subject (`id:`), or both operands match the whole subject (`idem`).
    pub(crate) fn match_(
        &self,
        rt: &Runtime,
        sig: &Signature,
        subject: DagId,
        ext_allowed: bool,
    ) -> Option<CuiSubproblem> {
        let sym = sig.symbol(self.symbol);
        let comm = sym.axioms.comm;
        let idem = sym.axioms.idem;
        let identity = sym.identity;
        let mut pairings: Vec<Pairing> = Vec::new();
        match &rt.node(subject).term {
            NodeTerm::Cui { symbol, args } if *symbol == self.symbol => {
                let (s1, s2) = (args[0], args[1]);
                if ext_allowed && identity.is_some() {
                    // Identity-first: the collapse-extension options precede the whole matches.
                    // The rewritten argument keeps its position beside the residue.
                    pairings.push(Pairing {
                        t1: Target::Dag(s1),
                        t2: Target::Identity,
                        residue: Some(CuiResidue::Second(s2)),
                    });
                    pairings.push(Pairing {
                        t1: Target::Dag(s2),
                        t2: Target::Identity,
                        residue: Some(CuiResidue::First(s1)),
                    });
                    pairings.push(Pairing {
                        t1: Target::Identity,
                        t2: Target::Dag(s1),
                        residue: Some(CuiResidue::Second(s2)),
                    });
                    pairings.push(Pairing {
                        t1: Target::Identity,
                        t2: Target::Dag(s2),
                        residue: Some(CuiResidue::First(s1)),
                    });
                }
                pairings.push(Pairing {
                    t1: Target::Dag(s1),
                    t2: Target::Dag(s2),
                    residue: None,
                });
                if comm {
                    pairings.push(Pairing {
                        t1: Target::Dag(s2),
                        t2: Target::Dag(s1),
                        residue: None,
                    });
                }
                // The collapse arms hold at an `f`-rooted subject too: `f(f(a, b), e)` equals
                // `f(a, b)` modulo the identity. They come last, so a first-solution consumer
                // reaches them only when no other pairing matches.
                push_collapse_pairings(&mut pairings, subject, identity.is_some(), idem);
            }
            _ => {
                push_collapse_pairings(&mut pairings, subject, identity.is_some(), idem);
                if pairings.is_empty() {
                    return None;
                }
            }
        }
        Some(CuiSubproblem {
            symbol: self.symbol,
            identity,
            p1: self.p1.clone(),
            p2: self.p2.clone(),
            var_indices: self.var_indices.clone(),
            pairings,
            solutions: None,
            cursor: 0,
            bound: Vec::new(),
            residue: None,
        })
    }
}

/// Append the collapse arms for `subject` (whole matches, no residue): one operand takes the
/// identity and the other the whole subject (`id:`), and both operands take the whole subject
/// (`idem`).
fn push_collapse_pairings(
    pairings: &mut Vec<Pairing>,
    subject: DagId,
    has_identity: bool,
    idem: bool,
) {
    if has_identity {
        pairings.push(Pairing {
            t1: Target::Dag(subject),
            t2: Target::Identity,
            residue: None,
        });
        pairings.push(Pairing {
            t1: Target::Identity,
            t2: Target::Dag(subject),
            residue: None,
        });
    }
    if idem {
        pairings.push(Pairing {
            t1: Target::Dag(subject),
            t2: Target::Dag(subject),
            residue: None,
        });
    }
}

/// One pattern-operand target: a subject node, or the operator's (cached, already-reduced)
/// identity dag — resolved lazily in `next` (building/refreshing the dag needs `&mut Runtime`).
#[derive(Clone, Copy)]
enum Target {
    Dag(DagId),
    Identity,
}

/// One way of pairing the two pattern operands with targets, with an optional unmatched residue
/// argument (the CUI collapse-extension case).
struct Pairing {
    t1: Target,
    t2: Target,
    residue: Option<CuiResidue>,
}

/// The unmatched subject argument of a collapse-extension match, tagged with the position it holds.
/// The rewritten argument keeps the other position. A non-commutative operator needs this: with
/// `eq t(A) # e = k(A)`, the subject `b # t(a)` becomes `b # k(a)`, not `k(a) # b`. Commutative
/// results are re-canonicalized by construction either way.
#[derive(Clone, Copy, Debug)]
pub(crate) enum CuiResidue {
    /// The residue is the first argument; the rewritten argument was the second.
    First(DagId),
    /// The residue is the second argument; the rewritten argument was the first.
    Second(DagId),
}

impl CuiResidue {
    /// The residue argument itself, independent of its position.
    fn arg(self) -> DagId {
        match self {
            CuiResidue::First(arg) | CuiResidue::Second(arg) => arg,
        }
    }

    /// Re-seat the instantiated `rhs` beside the residue, in the rewritten argument's position.
    pub(crate) fn rebuild(
        self,
        rt: &mut Runtime,
        sig: &Signature,
        symbol: SymbolId,
        rhs: DagId,
    ) -> DagId {
        match self {
            CuiResidue::First(residue) => rt.make_cui(sig, symbol, residue, rhs),
            CuiResidue::Second(residue) => rt.make_cui(sig, symbol, rhs, residue),
        }
    }
}

/// Collect the distinct variable indices of a (free) pattern term, in first-seen order.
fn collect_vars(t: &Term, out: &mut Vec<u32>) {
    match t {
        Term::Var(v) => {
            if !out.contains(&v.index) {
                out.push(v.index);
            }
        }
        Term::Na { .. } => {} // a literal introduces no variables
        Term::Op { args, .. } => {
            for a in args {
                collect_vars(a, out);
            }
        }
        Term::Iter { arg, .. } => collect_vars(arg, out),
    }
}

type CuiBindings = Vec<(u32, DagId)>;
type CuiSolution = (CuiBindings, Option<CuiResidue>);

/// A resumable enumerator over the deduped pairings (commutative, collapse, and collapse-extension) of
/// a [`CuiLhs`]. The pairings are enumerated lazily on the first [`next`](CuiSubproblem::next) — each
/// argument is matched through the full matcher seam, so a theory-rooted argument needs
/// `&mut Runtime` — then replayed.
pub(crate) struct CuiSubproblem {
    symbol: SymbolId,
    identity: Option<IdentityId>,
    p1: Term,
    p2: Term,
    var_indices: Vec<u32>,
    /// The pairing options, in match-preference order (collapse-extension first, rooted-subject
    /// collapse arms last).
    pairings: Vec<Pairing>,
    /// Deduped pairing solutions (bindings + the pairing's residue); `None` until the first `next`.
    solutions: Option<Vec<CuiSolution>>,
    cursor: usize,
    bound: Vec<u32>,
    /// The most recent solution's unmatched argument (collapse-extension), spliced by `build_result`.
    residue: Option<CuiResidue>,
}

impl CuiSubproblem {
    /// Install the next pairing's bindings into `subst`; `false` when exhausted. On the first call,
    /// enumerate every pairing — each as a length-2 alien sequence `[(p1, a), (p2, b)]` so
    /// theory-rooted arguments and non-linear variables compose correctly — deduping symmetric matches.
    pub(crate) fn next(&mut self, rt: &mut Runtime, sig: &Signature, subst: &mut Subst) -> bool {
        for &idx in &self.bound {
            subst.unbind(idx);
        }
        self.bound.clear();
        if self.solutions.is_none() {
            // Resolve Identity targets to the cached (already-reduced) identity dag now that
            // `&mut Runtime` is available — the reduced stamp is refreshed here, which is what
            // makes a bare-variable rhs bound to it one-shot (see Runtime::identity_dag).
            let id_dag = self.identity.map(|id_sym| rt.identity_dag(sig, id_sym));
            let resolve = |t: Target| match t {
                Target::Dag(d) => d,
                Target::Identity => id_dag.expect("Identity target only built when id: present"),
            };
            let mut sols: Vec<CuiSolution> = Vec::new();
            for p in &self.pairings {
                let (a, b) = (resolve(p.t1), resolve(p.t2));
                let aliens = [(self.p1.clone(), a), (self.p2.clone(), b)];
                for sol in enumerate_alien_solutions(rt, sig, subst, &aliens, &self.var_indices) {
                    // Distinct pairings can coincide for symmetric matches (`f(X, X) <=? f(a, a)`),
                    // or when both subject arguments are one shared node (`t(A) # e` on
                    // `t(a) # t(a)`); keep the first. The residue's position stays out of the key:
                    // two solutions that differ only there carry the same substitution, so keeping
                    // both would report one matcher twice.
                    let residue = p.residue.map(CuiResidue::arg);
                    if !sols
                        .iter()
                        .any(|(binds, r)| *binds == sol && r.map(CuiResidue::arg) == residue)
                    {
                        sols.push((sol, p.residue));
                    }
                }
            }
            self.solutions = Some(sols);
        }
        let (binds, residue) = {
            let sols = self.solutions.as_ref().expect("just enumerated");
            if self.cursor >= sols.len() {
                return false;
            }
            sols[self.cursor].clone()
        };
        self.cursor += 1;
        for &(idx, b) in &binds {
            subst.bind(idx, b);
            self.bound.push(idx);
        }
        self.residue = residue;
        true
    }

    pub(crate) fn rewrite_context(&self) -> RewriteMatchContext {
        match self.residue {
            Some(residue) => RewriteMatchContext::cui(self.symbol, residue),
            None => RewriteMatchContext::whole(),
        }
    }

    /// A whole match is just the instantiated rhs; a collapse-extension match re-seats the rhs
    /// beside the unmatched argument, in the matched argument's position (the CUI residue:
    /// `eq a * X = c` on `a * b` -> `b * c`; `eq a # X = c` on non-commutative `b # a` -> `b # c`).
    pub(crate) fn build_result(&self, rt: &mut Runtime, sig: &Signature, rhs: DagId) -> DagId {
        match self.residue {
            Some(residue) => residue.rebuild(rt, sig, self.symbol, rhs),
            None => rhs,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::Engine;

    /// `match f(X, Y) <=? f(a, b)` over `[comm]` yields both commutative pairings.
    #[test]
    fn cui_match_two_pairings() {
        let mut e = Engine::new();
        let s = e.add_sort("E");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let f = e.add_op_cui("f", vec![s, s], s, true, false, None);
        let (a0, b0) = (e.make_const(a), e.make_const(b));
        let subject = e.make_cui(f, a0, b0); // f(a, b)
        let pat = Term::op(f, vec![Term::var(0, s), Term::var(1, s)]);

        let lhs = CuiLhs::compile(pat, e.signature());
        let mut subst = Subst::new();
        subst.reset(2);
        let (sig, rt) = e.parts_mut();
        let mut sp = lhs
            .match_(rt, sig, subject, false)
            .expect("f(X,Y) matches f(a,b)");
        let mut got: Vec<(Option<DagId>, Option<DagId>)> = Vec::new();
        while sp.next(rt, sig, &mut subst) {
            got.push((subst.get(0), subst.get(1)));
        }
        // Decode to symbol-name pairs.
        let mut names: Vec<(String, String)> = got
            .iter()
            .map(|&(x, y)| {
                let nm = |id: DagId| e.symbol(e.node(id).symbol()).name().to_string();
                (nm(x.unwrap()), nm(y.unwrap()))
            })
            .collect();
        names.sort();
        assert_eq!(
            names,
            vec![("a".into(), "b".into()), ("b".into(), "a".into())],
            "two pairings: X=a/Y=b and X=b/Y=a"
        );
    }

    /// A collapse-extension match on the SECOND argument of a non-commutative `[id: e]` operator
    /// rewrites that argument in place: `a # X` and `X # a` on `b # a` take `X = e`, and the rhs `c`
    /// is re-seated as `b # c` (never `c # b`), by the matcher's own rebuild and by the detached
    /// rewrite context alike. The first-argument control `a # b` gives `c # b`.
    #[test]
    fn cui_collapse_extension_keeps_argument_order() {
        let mut e = Engine::new();
        let s = e.add_sort("S");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let c = e.add_op("c", vec![], s);
        let unit = e.add_op("e", vec![], s);
        let f = e.add_op_cui("_#_", vec![s, s], s, false, false, Some(unit));
        let (a0, b0, c0) = (e.make_const(a), e.make_const(b), e.make_const(c));
        let ba = e.make_cui(f, b0, a0);
        let ab = e.make_cui(f, a0, b0);
        let bc = e.make_cui(f, b0, c0);
        let cb = e.make_cui(f, c0, b0);
        let patterns = [
            Term::op(f, vec![Term::constant(a), Term::var(0, s)]), // a # X
            Term::op(f, vec![Term::var(0, s), Term::constant(a)]), // X # a
        ];
        for pat in patterns {
            let lhs = CuiLhs::compile(pat, e.signature());
            for (subject, want) in [(ba, bc), (ab, cb)] {
                let mut subst = Subst::new();
                subst.reset(1);
                let (built, detached, x) = {
                    let (sig, rt) = e.parts_mut();
                    let mut sp = lhs
                        .match_(rt, sig, subject, true)
                        .expect("the pattern collapse-matches one argument");
                    assert!(sp.next(rt, sig, &mut subst), "a first solution exists");
                    let built = sp.build_result(rt, sig, c0);
                    let detached = sp.rewrite_context().build_result(rt, sig, c0);
                    (built, detached, subst.get(0).expect("X is bound"))
                };
                assert_eq!(e.node(x).symbol(), unit, "the first solution is X = e");
                assert!(
                    e.deep_equal(built, want),
                    "build_result keeps argument order"
                );
                assert!(e.deep_equal(detached, want), "the rewrite context agrees");
            }
        }
    }

    /// At a subject rooted at the operator, the collapse arms follow the ordinary pairings. With
    /// `[id: e]`, `f(X, Y) <=? f(a, b)` also yields `X = f(a, b), Y = e` and `X = e, Y = f(a, b)`
    /// (the three solutions the CUI unifier returns for the same problem); `[comm id: e]` yields
    /// four; `idem` adds `X = Y = f(a, b)` after them.
    #[test]
    fn cui_rooted_subject_collapse_solutions() {
        let mut e = Engine::new();
        let s = e.add_sort("S");
        e.close_sorts();
        let a = e.add_op("a", vec![], s);
        let b = e.add_op("b", vec![], s);
        let unit = e.add_op("e", vec![], s);
        let (a0, b0, e0) = (e.make_const(a), e.make_const(b), e.make_const(unit));
        // (comm, idem, identity) for each operator under test.
        let theories = [
            (false, false, true),
            (true, false, true),
            (false, true, false),
            (true, true, false),
            (false, true, true),
        ];
        for (n, (comm, idem, identity)) in theories.into_iter().enumerate() {
            let f = e.add_op_cui(
                format!("f{n}"),
                vec![s, s],
                s,
                comm,
                idem,
                identity.then_some(unit),
            );
            let subject = e.make_cui(f, a0, b0);
            let (s1, s2) = match &e.node(subject).term {
                NodeTerm::Cui { args, .. } => (args[0], args[1]),
                _ => unreachable!("f(a, b) stays an f-rooted node"),
            };
            let mut want = vec![(s1, s2)];
            if comm {
                want.push((s2, s1));
            }
            if identity {
                want.push((subject, e0));
                want.push((e0, subject));
            }
            if idem {
                want.push((subject, subject));
            }

            let pat = Term::op(f, vec![Term::var(0, s), Term::var(1, s)]);
            let lhs = CuiLhs::compile(pat, e.signature());
            let mut subst = Subst::new();
            subst.reset(2);
            let mut got = Vec::new();
            {
                let (sig, rt) = e.parts_mut();
                let mut sp = lhs
                    .match_(rt, sig, subject, false)
                    .expect("f(X, Y) matches f(a, b)");
                while sp.next(rt, sig, &mut subst) {
                    got.push((subst.get(0).unwrap(), subst.get(1).unwrap()));
                }
            }
            assert_eq!(got.len(), want.len(), "solution count for f{n}");
            for (i, (&(x, y), &(wx, wy))) in got.iter().zip(&want).enumerate() {
                assert!(
                    e.deep_equal(x, wx) && e.deep_equal(y, wy),
                    "f{n} solution {i} out of place"
                );
            }
        }
    }
}
