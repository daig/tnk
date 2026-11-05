//! Resumable rewriting sessions: rule-fair `rewrite`, position-fair `frewrite`, and object-message-fair
//! `erewrite`.
//!
//! A [`Rewriting`] owns its current term (kept live by a [`RootGuard`]) and the round-robin rule
//! cursors, borrowing the [`Engine`] only per [`run`](Rewriting::run) call — so the REPL can store it
//! between commands to implement `continue`.

use crate::dag::DagId;
use crate::descent::{DescentOps, NullDescent};
use crate::engine::{ERewritePass, ERewritePassStep, Engine, SemanticCheckpoint};
use crate::external::{ExternalRequestToken, ExternalResponse, MetaEnvelope};
use crate::host::ReducerFault;
use crate::root::RootGuard;
use crate::symbol::SymbolId;
use std::collections::HashMap;

/// The traversal discipline of a [`Rewriting`] session.
#[derive(Clone, Copy)]
enum Mode {
    /// `rewrite`: rule-fair — reduce to canonical, then apply the first rule at the top-down-first redex.
    Rule,
    /// `frewrite`: position-fair — `gas` rule applications per non-frozen position per traversal pass.
    Position { gas: u64 },
    /// `erewrite`: at a `config` soup, deliver queued messages object-by-object; at any other node, fall
    /// back to position-fair rewriting. `gas` is the per-position gas for the non-config fallback.
    ObjectMessages { gas: u64 },
}

struct ObjectRunState {
    remaining: Option<u64>,
    pass: Option<ERewritePass>,
}

/// Result of driving an `erewrite` with host-owned external targets enabled.
pub enum ExternalRun {
    Complete(RewriteStep),
    Suspended {
        token: ExternalRequestToken,
        request: MetaEnvelope,
    },
}

/// A resumable rewriting session. Owns and roots its current term across reductions and REPL
/// `continue`s, and persists per-symbol round-robin rule cursors so each sequence cycles fairly.
/// The first [`ReducerFault`] terminally invalidates the session; every later fallible drive returns
/// the same fault.
pub struct Rewriting {
    current: DagId,
    root: RootGuard,
    cursors: HashMap<SymbolId, u32>,
    /// Set once a normal form is reached (no rule applies anywhere); a further `continue` is a no-op.
    done: bool,
    mode: Mode,
    object_run: Option<ObjectRunState>,
    next_external_request: u64,
    pending_external: Option<(ExternalRequestToken, MetaEnvelope)>,
    /// The first reducer fault terminally invalidates this resumable session.
    fault: Option<ReducerFault>,
}

struct RewritingCheckpoint {
    current: DagId,
    _root: RootGuard,
    /// Every `counter` operator's value at the start of the drive. Counters fire only inside these
    /// drives and are not part of the engine's `SemanticCheckpoint`, so a fault restores them here.
    counters: HashMap<SymbolId, u64>,
}

/// The outcome of one bounded [`Rewriting::run`]: the current term, whether a normal form was reached
/// (`done`), and whether the term's least sort is known. A bounded `frewrite` stop can leave a
/// non-canonical term whose sort has not been calculated.
#[derive(Debug)]
pub struct RewriteStep {
    pub term: DagId,
    pub done: bool,
    pub sort_known: bool,
}

impl Rewriting {
    /// Construct a rule-fair (`rewrite`) session rooted at `current`.
    pub(crate) fn new_rule_fair(root: RootGuard, current: DagId) -> Self {
        Rewriting {
            current,
            root,
            cursors: HashMap::new(),
            done: false,
            mode: Mode::Rule,
            object_run: None,
            next_external_request: 0,
            pending_external: None,
            fault: None,
        }
    }

    /// Construct a position-fair (`frewrite`) session rooted at `current`, with `gas` rule applications
    /// per position per pass.
    pub(crate) fn new_position_fair(root: RootGuard, current: DagId, gas: u64) -> Self {
        Rewriting {
            current,
            root,
            cursors: HashMap::new(),
            done: false,
            mode: Mode::Position { gas },
            object_run: None,
            next_external_request: 0,
            pending_external: None,
            fault: None,
        }
    }

    /// Construct an object-message-fair (`erewrite`) session rooted at `current`, with `gas` for the
    /// non-config fallback.
    pub(crate) fn new_object_message_fair(root: RootGuard, current: DagId, gas: u64) -> Self {
        Rewriting {
            current,
            root,
            cursors: HashMap::new(),
            done: false,
            mode: Mode::ObjectMessages { gas },
            object_run: None,
            next_external_request: 0,
            pending_external: None,
            fault: None,
        }
    }

    /// The current term.
    pub fn current(&self) -> DagId {
        self.current
    }

    /// Whether a normal form has been reached (no rule applies anywhere).
    pub fn is_done(&self) -> bool {
        self.done
    }
    /// Whether this session uses the EXTERNAL object-message scheduler.
    pub fn uses_external_messages(&self) -> bool {
        matches!(self.mode, Mode::ObjectMessages { .. })
    }

    /// Run up to `bound` rule applications (`None` = unbounded, to a normal form); `continue m` calls
    /// this again with `Some(m)`. Ordinary callers do not offer registered host targets.
    ///
    /// # Panics
    ///
    /// Panics if a configured strict reducer reports a [`ReducerFault`], or if this `erewrite`
    /// session has a suspended external request that must be answered through
    /// [`resume_external`](Self::resume_external).
    pub fn run(&mut self, engine: &mut Engine, bound: Option<u64>) -> RewriteStep {
        self.try_run(engine, bound)
            .unwrap_or_else(|fault| panic!("{fault}"))
    }

    /// Fallible form of [`run`](Self::run).
    ///
    /// # Panics
    ///
    /// Panics if this `erewrite` session has a suspended external request that must be answered
    /// through [`try_resume_external`](Self::try_resume_external).
    pub fn try_run(
        &mut self,
        engine: &mut Engine,
        bound: Option<u64>,
    ) -> Result<RewriteStep, ReducerFault> {
        if let Some(fault) = &self.fault {
            return Err(fault.clone());
        }
        if self.done {
            return Ok(self.completed_step());
        }
        let checkpoint = engine.semantic_checkpoint();
        let session_checkpoint = self.checkpoint(engine);
        let result = self.try_run_inner(engine, bound);
        self.finish_fallible(engine, checkpoint, session_checkpoint, result)
    }

    fn try_run_inner(
        &mut self,
        engine: &mut Engine,
        bound: Option<u64>,
    ) -> Result<RewriteStep, ReducerFault> {
        match self.mode {
            Mode::Rule => self.run_rule_fair(engine, bound),
            Mode::Position { gas } => self.run_position_fair(engine, bound, gas),
            Mode::ObjectMessages { gas } => {
                assert!(
                    self.pending_external.is_none(),
                    "a suspended external request must be resumed explicitly"
                );
                let mut descent = NullDescent;
                self.start_object_run(engine, bound, &mut descent)?;
                match self.drive_object_run(engine, gas, &mut descent, false)? {
                    ExternalRun::Complete(step) => Ok(step),
                    ExternalRun::Suspended { .. } => {
                        unreachable!("host targets are disabled for Rewriting::run")
                    }
                }
            }
        }
    }

    /// Start or observe an `erewrite` run with registered host targets enabled. Reaching such a target
    /// returns an owned request and leaves the parent scheduler suspended. The caller must answer through
    /// [`resume_external`](Self::resume_external); calling this method again simply returns the same token
    /// and request.
    ///
    /// # Panics
    ///
    /// Panics if a configured strict reducer reports a [`ReducerFault`].
    pub fn run_with_external(
        &mut self,
        engine: &mut Engine,
        bound: Option<u64>,
        descent: &mut dyn DescentOps,
    ) -> ExternalRun {
        self.try_run_with_external(engine, bound, descent)
            .unwrap_or_else(|fault| panic!("{fault}"))
    }

    /// Fallible form of [`run_with_external`](Self::run_with_external).
    pub fn try_run_with_external(
        &mut self,
        engine: &mut Engine,
        bound: Option<u64>,
        descent: &mut dyn DescentOps,
    ) -> Result<ExternalRun, ReducerFault> {
        if let Some(fault) = &self.fault {
            return Err(fault.clone());
        }
        if self.done {
            return Ok(ExternalRun::Complete(self.completed_step()));
        }
        if let Some((token, request)) = &self.pending_external {
            return Ok(ExternalRun::Suspended {
                token: *token,
                request: request.clone(),
            });
        }
        let checkpoint = engine.semantic_checkpoint();
        let session_checkpoint = self.checkpoint(engine);
        let result = match self.mode {
            Mode::ObjectMessages { gas } => match self.start_object_run(engine, bound, descent) {
                Ok(()) => self.drive_object_run(engine, gas, descent, true),
                Err(fault) => Err(fault),
            },
            _ => self.try_run_inner(engine, bound).map(ExternalRun::Complete),
        };
        self.finish_fallible(engine, checkpoint, session_checkpoint, result)
    }

    /// Resolve exactly the currently suspended external request, then continue the same pass and bound.
    /// `None` rejects the request and restores its message to the configuration. A stale/wrong token has
    /// no effect and returns `None`.
    ///
    /// # Panics
    ///
    /// Panics if a configured strict reducer reports a [`ReducerFault`].
    pub fn resume_external(
        &mut self,
        engine: &mut Engine,
        token: ExternalRequestToken,
        response: Option<ExternalResponse>,
        descent: &mut dyn DescentOps,
    ) -> Option<ExternalRun> {
        self.try_resume_external(engine, token, response, descent)
            .unwrap_or_else(|fault| panic!("{fault}"))
    }

    /// Fallible form of [`resume_external`](Self::resume_external).
    pub fn try_resume_external(
        &mut self,
        engine: &mut Engine,
        token: ExternalRequestToken,
        response: Option<ExternalResponse>,
        descent: &mut dyn DescentOps,
    ) -> Result<Option<ExternalRun>, ReducerFault> {
        if let Some(fault) = &self.fault {
            return Err(fault.clone());
        }
        let Some((pending, _)) = self.pending_external.as_ref() else {
            return Ok(None);
        };
        if *pending != token {
            return Ok(None);
        }
        let checkpoint = engine.semantic_checkpoint();
        let session_checkpoint = self.checkpoint(engine);
        self.pending_external = None;
        let Some(mut state) = self.object_run.take() else {
            return Ok(None);
        };
        let Some(pass) = state.pass.as_mut() else {
            return Ok(None);
        };
        let accepted = response.is_some_and(|response| {
            engine.accept_external_response(
                response.reply.as_ref(),
                response.rewrites,
                response.breakdown,
            )
        });
        engine.resolve_erewrite_external(pass, accepted);
        self.object_run = Some(state);
        let Mode::ObjectMessages { gas } = self.mode else {
            unreachable!("only erewrite can suspend externally")
        };
        let result = self.drive_object_run(engine, gas, descent, true).map(Some);
        self.finish_fallible(engine, checkpoint, session_checkpoint, result)
    }

    fn checkpoint(&self, engine: &Engine) -> RewritingCheckpoint {
        RewritingCheckpoint {
            current: self.current,
            _root: engine.root(self.current),
            counters: engine.counter_snapshot(),
        }
    }

    fn finish_fallible<T>(
        &mut self,
        engine: &mut Engine,
        checkpoint: SemanticCheckpoint,
        session_checkpoint: RewritingCheckpoint,
        result: Result<T, ReducerFault>,
    ) -> Result<T, ReducerFault> {
        match result {
            Ok(value) => Ok(value),
            Err(fault) => {
                engine.restore_semantic_checkpoint(checkpoint);
                engine.restore_counters(session_checkpoint.counters);
                self.current = session_checkpoint.current;
                self.root.set(session_checkpoint.current);
                self.done = true;
                self.cursors.clear();
                self.object_run = None;
                self.pending_external = None;
                self.fault = Some(fault.clone());
                Err(fault)
            }
        }
    }

    fn completed_step(&self) -> RewriteStep {
        RewriteStep {
            term: self.current,
            done: true,
            sort_known: true,
        }
    }

    /// `rewrite`: each step reduces `current` to canonical form, counting those equational rewrites,
    /// then applies one rule at the top-down-first redex.
    fn run_rule_fair(
        &mut self,
        engine: &mut Engine,
        bound: Option<u64>,
    ) -> Result<RewriteStep, ReducerFault> {
        let mut steps = 0u64;
        loop {
            let reduced = engine.try_reduce(self.current)?;
            self.current = reduced;
            self.root.set(reduced);
            if bound == Some(steps) {
                return Ok(RewriteStep {
                    term: self.current,
                    done: false,
                    sort_known: true,
                });
            }
            match engine.rewrite_step(self.current, &mut self.cursors)? {
                Some(next) => {
                    self.current = next;
                    self.root.set(next);
                    steps += 1;
                }
                None => {
                    self.done = true;
                    return Ok(RewriteStep {
                        term: self.current,
                        done: true,
                        sort_known: true,
                    });
                }
            }
        }
    }

    /// `frewrite`: position-fair. Reduce once, then repeat traversal passes, giving every non-frozen
    /// position up to `gas` rule applications with reduction between them, until the bound is hit or a
    /// pass makes no progress. A bounded stop leaves a non-canonical term with `sort_known = false`;
    /// the REPL reports it as `result (sort not calculated): …`.
    fn run_position_fair(
        &mut self,
        engine: &mut Engine,
        bound: Option<u64>,
        gas: u64,
    ) -> Result<RewriteStep, ReducerFault> {
        let mut remaining = bound;
        self.current = engine.try_reduce(self.current)?;
        self.root.set(self.current);
        loop {
            let mut progress = false;
            let next = engine.frewrite_pass(
                self.current,
                gas,
                &mut remaining,
                &mut progress,
                &mut self.cursors,
            )?;
            self.current = next;
            self.root.set(next);
            if remaining == Some(0) {
                return Ok(RewriteStep {
                    term: self.current,
                    done: false,
                    sort_known: false,
                });
            }
            if !progress {
                self.done = true;
                return Ok(RewriteStep {
                    term: self.current,
                    done: true,
                    sort_known: true,
                });
            }
        }
    }

    /// Start one resumable object-message run. Initialization happens once even if a pass suspends.
    fn start_object_run(
        &mut self,
        engine: &mut Engine,
        bound: Option<u64>,
        descent: &mut dyn DescentOps,
    ) -> Result<(), ReducerFault> {
        if self.object_run.is_some() {
            return Ok(());
        }
        self.current = engine.try_reduce_with(self.current, descent)?;
        self.root.set(self.current);
        self.object_run = Some(ObjectRunState {
            remaining: bound,
            pass: None,
        });
        Ok(())
    }

    /// Drive the active object-message run to a bounded/final result or one external safe point.
    fn drive_object_run(
        &mut self,
        engine: &mut Engine,
        gas: u64,
        descent: &mut dyn DescentOps,
        offer_external: bool,
    ) -> Result<ExternalRun, ReducerFault> {
        let mut state = self
            .object_run
            .take()
            .expect("object-message run must be initialized");
        loop {
            if state.remaining == Some(0) {
                return Ok(ExternalRun::Complete(RewriteStep {
                    term: self.current,
                    done: false,
                    sort_known: true,
                }));
            }

            if engine.is_config_node(self.current) {
                if state.pass.is_none() {
                    state.pass = Some(engine.begin_erewrite_pass(self.current));
                }
                let pass_step = engine.advance_erewrite_pass(
                    state.pass.as_mut().expect("pass was created"),
                    &mut self.cursors,
                    offer_external,
                    descent,
                )?;
                match pass_step {
                    ERewritePassStep::External { target, message } => {
                        let request = engine
                            .with_meta_ctx(|ctx| MetaEnvelope::capture(ctx, &[target, message]));
                        let Some(request) = request else {
                            engine.resolve_erewrite_external(
                                state.pass.as_mut().expect("pass is suspended"),
                                false,
                            );
                            continue;
                        };
                        let token = ExternalRequestToken(self.next_external_request);
                        self.next_external_request = self
                            .next_external_request
                            .checked_add(1)
                            .expect("external request token space exhausted");
                        self.pending_external = Some((token, request.clone()));
                        self.object_run = Some(state);
                        return Ok(ExternalRun::Suspended { token, request });
                    }
                    ERewritePassStep::Complete { term, progress } => {
                        self.current = engine.try_reduce_with(term, descent)?;
                        self.root.set(self.current);
                        state.pass = None;
                        if !progress {
                            self.done = true;
                            return Ok(ExternalRun::Complete(self.completed_step()));
                        }
                        if let Some(remaining) = &mut state.remaining {
                            *remaining -= 1;
                        }
                    }
                }
            } else {
                let mut progress = false;
                let next = engine.frewrite_pass(
                    self.current,
                    gas,
                    &mut state.remaining,
                    &mut progress,
                    &mut self.cursors,
                )?;
                self.current = engine.try_reduce_with(next, descent)?;
                self.root.set(self.current);
                if state.remaining == Some(0) {
                    return Ok(ExternalRun::Complete(RewriteStep {
                        term: self.current,
                        done: false,
                        sort_known: true,
                    }));
                }
                if !progress {
                    self.done = true;
                    return Ok(ExternalRun::Complete(self.completed_step()));
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::external::ExternalRewriteBreakdown;
    use crate::symbol::{MetaHooks, MetaOp, SpecialOp};
    use std::rc::Rc;

    #[test]
    fn external_request_continuation_and_target_teardown_survive_gc() {
        let mut engine = Engine::new();
        let configuration = engine.add_sort("Configuration");
        engine.close_sorts();

        let none = engine.add_op("none", vec![], configuration);
        let soup = engine.add_op_ac(
            "__",
            vec![configuration, configuration],
            configuration,
            Some(none),
        );
        engine.set_oo_flags(soup, true, false, false, false);
        let portal = engine.add_op("<>", vec![], configuration);
        engine.set_oo_flags(portal, false, false, false, true);
        let target = engine.add_op("child", vec![], configuration);
        let requester = engine.add_op("requester", vec![], configuration);
        let request = engine.add_op("request", vec![configuration, configuration], configuration);
        engine.set_oo_flags(request, false, false, true, false);
        let meta_hook = engine.add_op("%meta-hook", vec![], configuration);
        engine.set_special(
            meta_hook,
            SpecialOp::Meta {
                op: MetaOp::Unknown,
                hooks: Rc::new(MetaHooks::default()),
            },
        );
        engine.prepare_identities();

        let target_node = engine.make_const(target);
        let target_envelope = engine
            .with_meta_ctx(|ctx| MetaEnvelope::capture(ctx, &[target_node]))
            .expect("a ground target with META hooks is transportable");
        let registration = engine
            .register_external_target(&target_envelope)
            .expect("the transport target rebuilds in its source engine");

        let requester_node = engine.make_const(requester);
        let message = engine.make_node(request, vec![target_node, requester_node]);
        let portal_node = engine.make_const(portal);
        let initial = engine.make_acu(soup, vec![(portal_node, 1), (message, 1)]);
        let mut rewriting = engine.erewrite(initial, 1);
        let mut descent = NullDescent;

        let (token, captured) =
            match rewriting.run_with_external(&mut engine, Some(1), &mut descent) {
                ExternalRun::Suspended { token, request } => (token, request),
                ExternalRun::Complete(_) => panic!("registered target must suspend"),
            };
        assert_eq!(captured.root_count(), 2);

        engine.gc([]);
        let repeated = match rewriting.run_with_external(&mut engine, Some(1), &mut descent) {
            ExternalRun::Suspended { token, request } => (token, request),
            ExternalRun::Complete(_) => panic!("pending request must remain suspended"),
        };
        assert_eq!(repeated.0, token);
        assert_eq!(
            repeated.1.structural_key(&[
                repeated.1.root(0).expect("target root"),
                repeated.1.root(1).expect("message root"),
            ]),
            captured.structural_key(&[
                captured.root(0).expect("target root"),
                captured.root(1).expect("message root"),
            ])
        );

        assert!(
            rewriting
                .resume_external(
                    &mut engine,
                    ExternalRequestToken(token.0 + 1),
                    None,
                    &mut descent,
                )
                .is_none(),
            "a stale token cannot consume the pending request"
        );
        engine.gc([]);

        let response = ExternalResponse {
            reply: None,
            rewrites: 7,
            breakdown: ExternalRewriteBreakdown {
                membership_applications: 1,
                rule_rewrites: 2,
                variant_narrowing_steps: 1,
                narrowing_steps: 1,
            },
        };
        let step = match rewriting
            .resume_external(&mut engine, token, Some(response), &mut descent)
            .expect("the live token resumes")
        {
            ExternalRun::Complete(step) => step,
            ExternalRun::Suspended { .. } => panic!("the sole request was consumed"),
        };
        assert_eq!(engine.rewrites(), 7);
        assert_eq!(engine.rewrite_breakdown(), (1, 2, 1, 1));

        engine.gc([]);
        let live_with_target = engine.live_nodes();
        assert!(engine.unregister_external_target(registration));
        assert!(!engine.unregister_external_target(registration));
        assert!(engine.gc([]) > 0, "teardown releases the registered target");
        assert!(
            engine.live_nodes() < live_with_target,
            "the retained parent does not keep the detached target alive"
        );
        assert_eq!(engine.node(step.term).symbol(), portal);
        assert_eq!(rewriting.current(), step.term);
    }
}
