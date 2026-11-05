//! Order-sorted type system: the sort poset, **kinds** (connected components, each with a
//! synthesized error/top sort), and the subsort partial order [`Sorts::leq`].
//!
//! Builds the poset, connected components and synthesized error sorts, reflexive-transitive subsort
//! closure, and stable per-kind indices. Application least-sort resolution across overloaded operator
//! declarations lives in the crate-private `Signature`; symbolic unification builds its sort functions
//! from the same data in `sort_bdds`.

use crate::id::Id;
use std::collections::{BTreeMap, BTreeSet};

pub type SortId = Id<Sort>;
pub type KindId = Id<Kind>;

#[derive(Debug, Clone)]
pub struct Sort {
    pub name: String,
    /// `true` for the synthesized error/top sort of a kind.
    pub is_error: bool,
}

#[derive(Debug, Clone)]
pub struct Kind {
    /// User member sorts of this connected component (excludes the error sort).
    pub members: Vec<SortId>,
    /// The synthesized error/top sort: a supersort of every member.
    pub error: SortId,
    /// Component index order: error sort first, then maximal user sorts in DFS discovery order, then
    /// the remaining sorts by a declaration-ordered topological traversal. Supersorts precede
    /// subsorts. This order determines BDD sort encoding and observable unifier enumeration.
    pub index_order: Vec<SortId>,
}

/// The sort signature: declare sorts and subsort edges, then [`Sorts::close`] computes kinds and
/// the subsort closure. Immutable thereafter.
#[derive(Default)]
pub struct Sorts {
    sorts: Vec<Sort>,
    kinds: Vec<Kind>,
    /// Declared immediate supersorts: `up[sub]` lists each `sup` with `sub < sup`, in declaration order.
    up: Vec<Vec<SortId>>,
    /// Declared immediate subsorts: `down[sup]` lists each `sub` with `sub < sup`, in declaration
    /// order. Drives each component's index order.
    down: Vec<Vec<SortId>>,
    /// Computed: `geq[s]` = every `x` with `s <= x` (includes `s` and `s`'s kind error sort).
    geq: Vec<BTreeSet<SortId>>,
    /// Computed down-set for each sort, used by least-sort resolution.
    leqs: Vec<BTreeSet<SortId>>,
    kind_of: Vec<KindId>,
    /// Computed: each sort's index within its kind's [`Kind::index_order`] (error sorts get 0).
    component_index: Vec<u32>,
    closed: bool,
}

impl Sorts {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn add_sort(&mut self, name: impl Into<String>) -> SortId {
        assert!(!self.closed, "cannot add sorts after close()");
        let id = Id::from_raw(self.sorts.len() as u32);
        self.sorts.push(Sort {
            name: name.into(),
            is_error: false,
        });
        self.up.push(Vec::new());
        self.down.push(Vec::new());
        id
    }

    /// Declare `sub < sup` (an immediate subsort relation).
    pub fn add_subsort(&mut self, sub: SortId, sup: SortId) {
        assert!(!self.closed, "cannot add subsorts after close()");
        self.up[sub.index()].push(sup);
        self.down[sup.index()].push(sub);
    }

    /// Find a cycle in the declared subsort edges, which would make [`close`](Self::close) panic.
    /// Returns a witness path `[s0, s1, ..., s0]` with each `s_i < s_{i+1}` declared; a self-loop
    /// `A < A` yields `[A, A]`. The search visits sorts and edges in declaration order, so the witness
    /// is deterministic. Callable before `close`; frontends use it to reject an invalid signature
    /// with a diagnostic instead of reaching the closure's panic.
    pub fn subsort_cycle(&self) -> Option<Vec<SortId>> {
        #[derive(Clone, Copy, PartialEq)]
        enum Mark {
            Unvisited,
            OnPath,
            Done,
        }
        let n = self.up.len();
        let mut mark = vec![Mark::Unvisited; n];
        // Iterative DFS: each frame is (sort, index of the next supersort edge to follow).
        let mut path: Vec<(usize, usize)> = Vec::new();
        for root in 0..n {
            if mark[root] != Mark::Unvisited {
                continue;
            }
            mark[root] = Mark::OnPath;
            path.push((root, 0));
            while let Some(frame) = path.last_mut() {
                let (s, next) = *frame;
                let Some(&sup) = self.up[s].get(next) else {
                    mark[s] = Mark::Done;
                    path.pop();
                    continue;
                };
                frame.1 += 1;
                let t = sup.index();
                match mark[t] {
                    Mark::Done => {}
                    Mark::Unvisited => {
                        mark[t] = Mark::OnPath;
                        path.push((t, 0));
                    }
                    Mark::OnPath => {
                        let start = path
                            .iter()
                            .position(|&(x, _)| x == t)
                            .expect("an on-path sort is on the DFS path");
                        let mut cycle: Vec<SortId> = path[start..]
                            .iter()
                            .map(|&(x, _)| Id::from_raw(x as u32))
                            .collect();
                        cycle.push(sup);
                        return Some(cycle);
                    }
                }
            }
        }
        None
    }

    pub fn sort(&self, s: SortId) -> &Sort {
        &self.sorts[s.index()]
    }
    pub fn name(&self, s: SortId) -> &str {
        &self.sorts[s.index()].name
    }
    pub fn kind_of(&self, s: SortId) -> KindId {
        debug_assert!(self.closed);
        self.kind_of[s.index()]
    }
    pub fn kind(&self, k: KindId) -> &Kind {
        &self.kinds[k.index()]
    }
    pub fn error_sort(&self, k: KindId) -> SortId {
        self.kinds[k.index()].error
    }
    pub fn num_sorts(&self) -> usize {
        self.sorts.len()
    }
    pub fn num_kinds(&self) -> usize {
        self.kinds.len()
    }

    /// Every kind id (connected component) in declaration order. Lets a frontend enumerate kinds to,
    /// e.g., expand a `poly`/`Universal` operator into one concrete instance per kind
    /// ([`error_sort`](Self::error_sort) gives each kind's top sort). Requires [`close`](Self::close).
    pub fn kinds(&self) -> impl Iterator<Item = KindId> + '_ {
        debug_assert!(self.closed);
        (0..self.kinds.len()).map(|i| KindId::from_raw(i as u32))
    }

    /// `a <= b` in the subsort order. Requires [`close`](Self::close).
    pub fn leq(&self, a: SortId, b: SortId) -> bool {
        debug_assert!(self.closed, "leq before close()");
        self.geq[a.index()].contains(&b)
    }

    /// Return every `y` with `y <= s`. Least-sort resolution intersects these down-sets.
    /// Requires [`close`](Self::close).
    pub(crate) fn down_set(&self, s: SortId) -> &BTreeSet<SortId> {
        debug_assert!(self.closed, "down_set before close()");
        &self.leqs[s.index()]
    }

    /// The **strict** subsorts of `s`: every sort `y != s` with `y <= s`. The `omod` object-pattern
    /// completion recovers the class sorts as the strict subsorts of `Cid` (a class `C` is declared with
    /// `subsort C < Cid`), so a class *constant* / class-sorted variable is recognized structurally.
    /// Requires [`close`](Self::close).
    pub(crate) fn strict_subsorts(&self, s: SortId) -> Vec<SortId> {
        self.down_set(s)
            .iter()
            .copied()
            .filter(|&y| y != s)
            .collect()
    }

    /// `true` if `a` and `b` are in the same kind (connected component).
    pub fn same_kind(&self, a: SortId, b: SortId) -> bool {
        self.kind_of(a) == self.kind_of(b)
    }

    /// A sort's index within its kind's [`Kind::index_order`]. Error sorts are index 0.
    /// Requires [`close`](Self::close).
    pub fn component_index(&self, s: SortId) -> u32 {
        debug_assert!(self.closed, "component_index before close()");
        self.component_index[s.index()]
    }

    /// Build a deterministic supersort-first linear extension for one kind. Index 0 is the error
    /// sort. Registration starts at the first-declared member, visits declared subsorts before
    /// supersorts, appends maximal sorts as they are reached, and records each non-maximal sort's
    /// unresolved supersort count. Scanning the growing order then appends each declared subsort
    /// when its final supersort has been processed. Only user-declared edges participate; the
    /// synthesized error sort remains outside the traversal.
    fn kind_index_order(
        up: &[Vec<SortId>],
        down: &[Vec<SortId>],
        members: &[SortId],
        error: SortId,
    ) -> Vec<SortId> {
        let mut order: Vec<SortId> = vec![error];
        let mut registered: BTreeSet<SortId> = BTreeSet::new();
        let mut unresolved: BTreeMap<SortId, usize> = BTreeMap::new();

        fn register(
            s: SortId,
            up: &[Vec<SortId>],
            down: &[Vec<SortId>],
            order: &mut Vec<SortId>,
            registered: &mut BTreeSet<SortId>,
            unresolved: &mut BTreeMap<SortId, usize>,
        ) {
            if !registered.insert(s) {
                return;
            }
            for &sub in &down[s.index()] {
                register(sub, up, down, order, registered, unresolved);
            }
            let sups = &up[s.index()];
            if sups.is_empty() {
                order.push(s);
            } else {
                unresolved.insert(s, sups.len());
                for &sup in sups {
                    register(sup, up, down, order, registered, unresolved);
                }
            }
        }
        register(
            members[0],
            up,
            down,
            &mut order,
            &mut registered,
            &mut unresolved,
        );

        let mut i = 1;
        while i < order.len() {
            let s = order[i];
            for &sub in &down[s.index()] {
                let n = unresolved
                    .get_mut(&sub)
                    .expect("registered non-maximal sort has an unresolved count");
                *n -= 1;
                if *n == 0 {
                    order.push(sub);
                }
            }
            i += 1;
        }
        assert_eq!(
            order.len(),
            members.len() + 1,
            "component could not be linearly ordered (subsort cycle)"
        );
        order
    }

    /// Compute kinds (connected components + error sorts) and the subsort closure.
    pub fn close(&mut self) {
        assert!(!self.closed, "already closed");
        let n0 = self.sorts.len();

        // 1. Connected components over the *undirected* subsort graph (union-find with halving).
        fn find(p: &mut [usize], mut x: usize) -> usize {
            while p[x] != x {
                p[x] = p[p[x]];
                x = p[x];
            }
            x
        }
        let mut parent: Vec<usize> = (0..n0).collect();
        for sub in 0..n0 {
            for sup in self.up[sub].clone() {
                let a = find(&mut parent, sub);
                let b = find(&mut parent, sup.index());
                if a != b {
                    parent[a] = b;
                }
            }
        }

        // 2. Group members by component root (BTreeMap → deterministic order).
        let mut groups: BTreeMap<usize, Vec<SortId>> = BTreeMap::new();
        for s in 0..n0 {
            let r = find(&mut parent, s);
            groups.entry(r).or_default().push(Id::from_raw(s as u32));
        }

        // 3. One error sort + kind per component.
        let mut kind_of: Vec<KindId> = vec![Id::from_raw(0); n0];
        for members in groups.into_values() {
            let kid: KindId = Id::from_raw(self.kinds.len() as u32);
            // Name the kind after its maximal sorts (those with no user supersort), listed in
            // component index order. This keeps kind-level output deterministic and aligns displayed
            // names with the sort indices used by unifier enumeration.
            let err: SortId = Id::from_raw(self.sorts.len() as u32);
            self.sorts.push(Sort {
                name: String::new(),
                is_error: true,
            }); // name filled once ordered
            self.up.push(Vec::new());
            self.down.push(Vec::new());
            for &m in &members {
                kind_of[m.index()] = kid;
            }
            let index_order = Self::kind_index_order(&self.up, &self.down, &members, err);
            // The maximal sorts are exactly `index_order`'s entries (after the error sort) with empty `up`.
            let repr = index_order
                .iter()
                .filter(|&&s| s != err && self.up[s.index()].is_empty())
                .map(|&s| self.sorts[s.index()].name.clone())
                .collect::<Vec<_>>()
                .join(",");
            self.sorts[err.index()].name = format!("[{repr}]");
            self.kinds.push(Kind {
                members,
                error: err,
                index_order,
            });
        }

        // 4. Subsort closure: BFS upward for each user sort, then add its kind's error sort.
        let n = self.sorts.len();
        let mut geq: Vec<BTreeSet<SortId>> = vec![BTreeSet::new(); n];
        for s in 0..n0 {
            let mut seen: BTreeSet<SortId> = BTreeSet::new();
            let mut stack = vec![Id::<Sort>::from_raw(s as u32)];
            while let Some(x) = stack.pop() {
                if seen.insert(x) {
                    stack.extend_from_slice(&self.up[x.index()]);
                }
            }
            seen.insert(self.kinds[kind_of[s].index()].error);
            geq[s] = seen;
        }

        // 4b. Reject mutually reachable distinct user sorts so the subsort relation remains a
        // partial order.
        for s in 0..n0 {
            let sid = Id::<Sort>::from_raw(s as u32);
            for &t in &geq[s] {
                if t != sid && t.index() < n0 && geq[t.index()].contains(&sid) {
                    panic!(
                        "subsort cycle: `{}` and `{}` are mutually <=",
                        self.sorts[s].name,
                        self.sorts[t.index()].name
                    );
                }
            }
        }

        // 5. Finalize kind_of including error sorts; error sorts are <= only themselves.
        let mut kind_of_full: Vec<KindId> = vec![Id::from_raw(0); n];
        kind_of_full[..n0].copy_from_slice(&kind_of);
        for (ki, k) in self.kinds.iter().enumerate() {
            kind_of_full[k.error.index()] = Id::from_raw(ki as u32);
            geq[k.error.index()].insert(k.error);
        }

        // 6. Invert `geq` into down-sets: `leqs[r] = { y : y <= r }` (since `y <= r` iff `r ∈ geq[y]`).
        let mut leqs: Vec<BTreeSet<SortId>> = vec![BTreeSet::new(); n];
        for (y, up) in geq.iter().enumerate() {
            let yid = Id::<Sort>::from_raw(y as u32);
            for &r in up {
                leqs[r.index()].insert(yid);
            }
        }

        // 7. Per-kind component indices (inverse of each kind's `index_order`).
        let mut component_index: Vec<u32> = vec![0; n];
        for k in &self.kinds {
            for (i, &s) in k.index_order.iter().enumerate() {
                component_index[s.index()] = i as u32;
            }
        }

        self.geq = geq;
        self.leqs = leqs;
        self.kind_of = kind_of_full;
        self.component_index = component_index;
        self.closed = true;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn subsort_order_and_kinds() {
        let mut s = Sorts::new();
        let zero = s.add_sort("Zero");
        let nznat = s.add_sort("NzNat");
        let nat = s.add_sort("Nat");
        let boolean = s.add_sort("Bool"); // separate component
        s.add_subsort(zero, nat);
        s.add_subsort(nznat, nat);
        s.close();

        // reflexivity + declared + (none transitive here beyond declared)
        assert!(s.leq(nat, nat));
        assert!(s.leq(zero, nat));
        assert!(s.leq(nznat, nat));
        assert!(!s.leq(nat, zero));
        assert!(!s.leq(zero, nznat));

        // kinds: Nat-family together, Bool apart
        assert!(s.same_kind(zero, nat));
        assert!(s.same_kind(nznat, nat));
        assert!(!s.same_kind(boolean, nat));
        assert!(!s.leq(boolean, nat));
        assert_eq!(s.num_kinds(), 2);
    }

    #[test]
    fn every_sort_is_below_its_kind_error() {
        let mut s = Sorts::new();
        let a = s.add_sort("A");
        let b = s.add_sort("B");
        s.add_subsort(a, b);
        s.close();

        let k = s.kind_of(a);
        let err = s.error_sort(k);
        assert!(s.sort(err).is_error);
        assert!(s.leq(a, err));
        assert!(s.leq(b, err));
        assert_eq!(s.kind_of(b), k);
        assert_eq!(s.kind_of(err), k);
        // the error sort is maximal: not below any proper sort
        assert!(!s.leq(err, a));
        assert!(!s.leq(err, b));
    }

    #[test]
    fn transitive_closure() {
        let mut s = Sorts::new();
        let a = s.add_sort("A");
        let mid = s.add_sort("Mid");
        let top = s.add_sort("Top");
        s.add_subsort(a, mid);
        s.add_subsort(mid, top);
        s.close();
        assert!(s.leq(a, top), "a <= mid <= top should imply a <= top");
        assert!(s.leq(a, mid));
        assert!(!s.leq(top, a));
    }

    /// Component indices put the error sort first, then DFS-discovered maximal sorts, then the
    /// declaration-ordered topological remainder.
    #[test]
    fn component_index_order_diamond() {
        // Diamond declared bottom-up: A < B, A < C, B < D, C < D.
        let mut s = Sorts::new();
        let a = s.add_sort("A");
        let b = s.add_sort("B");
        let c = s.add_sort("C");
        let d = s.add_sort("D");
        s.add_subsort(a, b);
        s.add_subsort(a, c);
        s.add_subsort(b, d);
        s.add_subsort(c, d);
        s.close();

        let k = s.kind(s.kind_of(a));
        let err = k.error;
        // DFS from A (first declared): A defers (has supersorts), B defers, D is maximal →
        // appended; Kahn from D releases B then C (declaration order of D's subsort list),
        // then A when C (its last unresolved supersort) is processed.
        assert_eq!(k.index_order, vec![err, d, b, c, a]);
        assert_eq!(s.component_index(err), 0);
        assert_eq!(s.component_index(d), 1);
        assert_eq!(s.component_index(b), 2);
        assert_eq!(s.component_index(c), 3);
        assert_eq!(s.component_index(a), 4);

        // The order is a linear extension with supersorts first: s <= t ⇒ index(s) >= index(t).
        for &x in &k.index_order {
            for &y in &k.index_order {
                if s.leq(x, y) {
                    assert!(
                        s.component_index(x) >= s.component_index(y),
                        "linear extension violated: {} <= {}",
                        s.name(x),
                        s.name(y)
                    );
                }
            }
        }
    }

    /// Maximal sorts follow the DFS visit order induced by declared subsort edges. Reversing those
    /// declarations reverses both their component indices and their order in the kind's printed name.
    #[test]
    fn component_index_order_follows_declaration_order() {
        let build = |flip: bool| {
            let mut s = Sorts::new();
            let bot = s.add_sort("Bot");
            let ta = s.add_sort("TopA");
            let tb = s.add_sort("TopB");
            if flip {
                s.add_subsort(bot, tb);
                s.add_subsort(bot, ta);
            } else {
                s.add_subsort(bot, ta);
                s.add_subsort(bot, tb);
            }
            s.close();
            let k = s.kind(s.kind_of(bot));
            k.index_order
                .iter()
                .map(|&x| s.name(x).to_string())
                .collect::<Vec<_>>()
        };
        assert_eq!(build(false), vec!["[TopA,TopB]", "TopA", "TopB", "Bot"]);
        assert_eq!(build(true), vec!["[TopB,TopA]", "TopB", "TopA", "Bot"]);
    }

    /// A singleton component: just the error sort above the lone member.
    #[test]
    fn component_index_order_singleton() {
        let mut s = Sorts::new();
        let solo = s.add_sort("Solo");
        s.close();
        let k = s.kind(s.kind_of(solo));
        assert_eq!(k.index_order, vec![k.error, solo]);
        assert_eq!(s.component_index(solo), 1);
    }

    #[test]
    fn subsort_cycle_witness() {
        let mut s = Sorts::new();
        let a = s.add_sort("A");
        let b = s.add_sort("B");
        let c = s.add_sort("C");
        let d = s.add_sort("D");
        s.add_subsort(d, a);
        s.add_subsort(a, b);
        s.add_subsort(b, c);
        assert_eq!(s.subsort_cycle(), None);
        s.add_subsort(c, a);
        assert_eq!(s.subsort_cycle(), Some(vec![a, b, c, a]));

        let mut s = Sorts::new();
        let x = s.add_sort("X");
        s.add_subsort(x, x);
        assert_eq!(s.subsort_cycle(), Some(vec![x, x]));

        // A diamond is acyclic even though `Bot` reaches `Top` twice.
        let mut s = Sorts::new();
        let bot = s.add_sort("Bot");
        let l = s.add_sort("L");
        let r = s.add_sort("R");
        let top = s.add_sort("Top");
        s.add_subsort(bot, l);
        s.add_subsort(bot, r);
        s.add_subsort(l, top);
        s.add_subsort(r, top);
        assert_eq!(s.subsort_cycle(), None);
    }

    #[test]
    #[should_panic(expected = "subsort cycle")]
    fn subsort_cycle_is_rejected() {
        let mut s = Sorts::new();
        let a = s.add_sort("A");
        let b = s.add_sort("B");
        s.add_subsort(a, b);
        s.add_subsort(b, a);
        s.close();
    }
}
