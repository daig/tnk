//! Symbolic root rewriting modulo SMT.
//!
//! States are `(term, accumulated constraint, path-local fresh counter)` triples. Breadth-first
//! expansion does not hash-cons states, because paths reaching the same term under distinct
//! constraints remain distinct.

use crate::dag::DagId;
use crate::engine::{Engine, RawSmtGoalMatch, RawSmtSuccessor};
use crate::num::Nat;
use crate::root::RootGuard;
use crate::search::Arrow;
use crate::smt::{ConfiguredSmtEngine, SmtEngine, SmtResult};
use crate::theory::LhsAutomaton;
use std::collections::VecDeque;

struct State {
    term: DagId,
    _term_root: RootGuard,
    constraint: DagId,
    _constraint_root: RootGuard,
    avoid_variable_number: Nat,
    depth: u32,
}

struct Expanding {
    state: usize,
    raw: Vec<RawSmtSuccessor>,
    cursor: usize,
}

/// One accepted symbolic state/goal match.
pub struct SmtSolution {
    pub number: u32,
    pub state: usize,
    pub bindings: Vec<DagId>,
    pub constraint: DagId,
    pub rewrites: u64,
    pub max_variable_number: Nat,
    _constraint_root: RootGuard,
}

/// Resumable breadth-first `smt-search` session.
pub struct SmtSearch {
    states: Vec<State>,
    arrow: Arrow,
    goal: LhsAutomaton,
    goal_nr_vars: u32,
    goal_smt_variables: Vec<(u32, DagId)>,
    max_depth: Option<u32>,
    frontier: VecDeque<usize>,
    expanding: Option<Expanding>,
    pending: VecDeque<SmtSolution>,
    solution_count: u32,
    tested_initial: bool,
    solver: ConfiguredSmtEngine,
    variable_names: Vec<String>,
    next_variable_slot: u32,
}

impl SmtSearch {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        engine: &mut Engine,
        initial: DagId,
        initial_constraint: DagId,
        goal: LhsAutomaton,
        goal_nr_vars: u32,
        goal_smt_variables: Vec<(u32, DagId)>,
        arrow: Arrow,
        max_depth: Option<u32>,
        variable_names: Vec<String>,
        initial_avoid_variable_number: Nat,
    ) -> Self {
        let state = State {
            term: initial,
            _term_root: engine.root(initial),
            constraint: initial_constraint,
            _constraint_root: engine.root(initial_constraint),
            avoid_variable_number: initial_avoid_variable_number,
            depth: 0,
        };
        let next_variable_slot = variable_names.len() as u32;
        Self {
            states: vec![state],
            arrow,
            goal,
            goal_nr_vars,
            goal_smt_variables,
            max_depth,
            frontier: VecDeque::from([0]),
            expanding: None,
            pending: VecDeque::new(),
            solution_count: 0,
            tested_initial: false,
            solver: ConfiguredSmtEngine::default(),
            variable_names,
            next_variable_slot,
        }
    }

    /// Variable-slot display names for symbolic states and final constraints. Fresh names are appended
    /// as accepted transitions introduce them.
    pub fn variable_names(&self) -> &[String] {
        &self.variable_names
    }

    pub fn state_term(&self, state: usize) -> Option<DagId> {
        self.states.get(state).map(|s| s.term)
    }

    pub fn next_solution(&mut self, engine: &mut Engine) -> Option<SmtSolution> {
        if !self.tested_initial {
            self.tested_initial = true;
            if self.arrow == Arrow::Star {
                // Like every other retained match, an initial-state goal match needs the backend's
                // `Sat` for the initial `such that` constraint, so an unverified (`Unsat`, `Unknown`,
                // or `BadDag`) initial constraint yields no match. Exempting the literal `true`
                // constraint, which the null backend answers `Unknown`, is provisional pending the
                // trivial-constraint decision recorded in TNK-DEV-012. Prepare the solver first in
                // every case: goal match constraints are checked against the initial constraint.
                let feasible = self.prepare_solver(engine, 0);
                if feasible || engine.is_smt_true(self.states[0].constraint) {
                    self.queue_goal_matches(engine, 0);
                }
            }
        }
        loop {
            if let Some(solution) = self.pending.pop_front() {
                return Some(solution);
            }
            if !self.step(engine) {
                return None;
            }
        }
    }

    fn step(&mut self, engine: &mut Engine) -> bool {
        if self.expanding.is_none() {
            let Some(state) = self.frontier.pop_front() else {
                return false;
            };
            if !self.may_expand(state) {
                return true;
            }
            if !self.prepare_solver(engine, state) {
                return true;
            }
            let raw = engine.smt_state_successors(
                self.states[state].term,
                &self.states[state].avoid_variable_number,
                &mut self.next_variable_slot,
            );
            self.expanding = Some(Expanding {
                state,
                raw,
                cursor: 0,
            });
        }

        let expanding = self.expanding.as_mut().expect("SMT expansion initialized");
        if expanding.cursor == expanding.raw.len() {
            self.expanding = None;
            return true;
        }
        let candidate = &expanding.raw[expanding.cursor];
        expanding.cursor += 1;
        let parent = expanding.state;

        self.solver.push();
        let satisfiable = match candidate.local_constraint {
            Some(constraint) => self.solver.assert_dag(engine, constraint) == SmtResult::Sat,
            None => true,
        };
        if !satisfiable {
            self.solver.pop();
            return true;
        }

        for &(slot, ref name) in &candidate.fresh_names {
            let slot = slot as usize;
            if self.variable_names.len() <= slot {
                self.variable_names.resize(slot + 1, String::new());
            }
            self.variable_names[slot] = name.clone();
        }
        let constraint = engine
            .smt_conjoin_constraints(self.states[parent].constraint, candidate.local_constraint);
        engine.count_smt_rewrite();
        let state = self.states.len();
        self.states.push(State {
            term: candidate.term,
            _term_root: engine.root(candidate.term),
            constraint,
            _constraint_root: engine.root(constraint),
            avoid_variable_number: candidate.avoid_variable_number.clone(),
            depth: self.states[parent].depth + 1,
        });
        self.frontier.push_back(state);
        self.queue_goal_matches(engine, state);
        self.solver.pop();
        true
    }

    fn may_expand(&self, state: usize) -> bool {
        let depth = self.states[state].depth;
        if self.arrow == Arrow::One && depth >= 1 {
            return false;
        }
        self.max_depth.is_none_or(|max| depth < max)
    }

    fn prepare_solver(&mut self, engine: &Engine, state: usize) -> bool {
        self.solver.clear();
        self.solver
            .assert_dag(engine, self.states[state].constraint)
            == SmtResult::Sat
    }

    fn queue_goal_matches(&mut self, engine: &mut Engine, state: usize) {
        let qualifies = match self.arrow {
            Arrow::One => self.states[state].depth == 1,
            Arrow::Plus => self.states[state].depth >= 1,
            Arrow::Star => true,
            Arrow::Bang => false,
        };
        if !qualifies {
            return;
        }
        let matches: Vec<RawSmtGoalMatch> = engine.smt_goal_matches(
            &self.goal,
            self.goal_nr_vars,
            &self.goal_smt_variables,
            self.states[state].term,
        );
        for matched in matches {
            if matched.match_constraint.is_some_and(|constraint| {
                self.solver.check_dag(engine, constraint) != SmtResult::Sat
            }) {
                continue;
            }
            let constraint = engine.smt_conjoin_goal_constraints(
                self.states[state].constraint,
                matched.match_constraint,
            );
            self.solution_count += 1;
            self.pending.push_back(SmtSolution {
                number: self.solution_count,
                state,
                bindings: matched.bindings,
                constraint,
                rewrites: engine.rewrites(),
                max_variable_number: self.states[state].avoid_variable_number.clone(),
                _constraint_root: engine.root(constraint),
            });
        }
    }
}
