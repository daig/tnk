use std::path::PathBuf;
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{SystemTime, UNIX_EPOCH};

use tnk_session::Session;

static NEXT_SCRATCH: AtomicU64 = AtomicU64::new(0);

/// A fresh, empty directory under the system temporary directory, unique to this test process.
fn scratch_dir(label: &str) -> PathBuf {
    let timestamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock must follow the Unix epoch")
        .as_nanos();
    let dir = std::env::temp_dir().join(format!(
        "tnk-session-{label}-{}-{timestamp}-{}",
        std::process::id(),
        NEXT_SCRATCH.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).expect("create scratch directory");
    dir
}

#[test]
fn host_session_persists_modules_and_current_selection() {
    let mut session = Session::new();

    let entered = session.eval(
        "fmod HOST-SESSION is sort N . ops zero one : -> N [ctor] . op plus : N N -> N . eq plus(zero, one) = one . endfm",
        false,
    );
    assert!(!entered.exit);
    assert_eq!(session.current(), Some("HOST-SESSION"));

    let reduced = session.eval("reduce plus(zero, one) .", false);
    assert!(!reduced.exit);
    assert!(reduced.output.contains("reduce in HOST-SESSION :"));
    assert!(reduced.output.contains("rewrites: 1"));
    assert!(reduced.output.contains("result N: one"));
}

#[test]
fn direct_session_reports_rewrite_breakdowns_for_reduce_and_search() {
    let mut session = Session::new();
    let entered = session.eval(
        "mod BREAKDOWN is
           sort State .
           ops a b c : -> State [ctor] .
           op f : State -> State .
           eq f(a) = a .
           rl [a-b] : a => b .
           rl [a-c] : a => c .
         endm
         set show breakdown on .",
        false,
    );
    assert!(!entered.exit);

    let reduced = session.eval("reduce f(a) .", false);
    assert!(reduced.output.contains(
        "mb applications: 0  equational rewrites: 1  rule rewrites: 0  \
         variant narrowing steps: 0  narrowing steps: 0"
    ));

    let searched = session.eval("search [3] a =>* X:State .", false);
    assert!(
        searched.output.contains(
            "states: 2  rewrites: 1\n\
             mb applications: 0  equational rewrites: 0  rule rewrites: 1  \
             variant narrowing steps: 0  narrowing steps: 0"
        ),
        "{}",
        searched.output
    );
}

#[test]
fn redefining_strategy_donor_rebuilds_existing_importer() {
    let mut session = Session::new();
    let entered = session.eval(
        "mod STRAT-INVALIDATION-COMMON is
           sort S .
           ops a b c : -> S .
           rl [to-b] : a => b .
           rl [to-c] : a => c .
         endm
         smod STRAT-INVALIDATION-BASE is
           protecting STRAT-INVALIDATION-COMMON .
           strat go : @ S .
           sd go := to-b .
         endsm
         smod STRAT-INVALIDATION-USE is
           protecting STRAT-INVALIDATION-BASE .
         endsm",
        false,
    );
    assert!(!entered.exit);

    let before = session.eval("srewrite in STRAT-INVALIDATION-USE : a using go .", false);
    assert!(before.output.contains("result S: b"), "{}", before.output);

    let redefined = session.eval(
        "smod STRAT-INVALIDATION-BASE is
           protecting STRAT-INVALIDATION-COMMON .
           strat go : @ S .
           sd go := to-c .
         endsm",
        false,
    );
    assert!(!redefined.exit);

    let after = session.eval("srewrite in STRAT-INVALIDATION-USE : a using go .", false);
    assert!(after.output.contains("result S: c"), "{}", after.output);
    assert!(!after.output.contains("result S: b"), "{}", after.output);
}

#[test]
fn parser_effort_limit_reports_once_and_session_recovers() {
    let mut session = Session::new();
    let mut module = String::from(
        "fmod PARSE-EFFORT-RECOVERY is
           sort S .
           op a : -> S [ctor] .
",
    );
    for index in 0..500 {
        module.push_str(&format!("op _o{index}_ : S S -> S [assoc] .\n"));
    }
    module.push_str("endfm");
    let entered = session.eval(&module, false);
    assert!(!entered.exit, "{}", entered.output);
    assert_eq!(session.current(), Some("PARSE-EFFORT-RECOVERY"));

    let mut command = String::from("reduce a");
    for _ in 1..640 {
        command.push_str(" o0 a");
    }
    command.push_str(" o0 bogus .\nreduce a .");
    let recovered = session.eval(&command, false);
    assert!(!recovered.exit);
    assert_eq!(
        recovered
            .output
            .matches("parse effort limit exceeded at token")
            .count(),
        1,
        "{}",
        recovered.output
    );

    assert!(
        recovered.output.contains("result S: a"),
        "{}",
        recovered.output
    );
}

/// TNK-SORT-001: a subsort cycle invalidates the signature. Each cyclic definition is rejected with
/// an ordinary `error:` diagnostic (no panic), is not installed, and later input still runs.
#[test]
fn cyclic_subsorts_are_rejected_atomically_and_session_recovers() {
    let mut session = Session::new();
    let entered = session.eval(
        "fmod CYCLE-BASE is
           sorts A B .
           subsort A < B .
           op a : -> A [ctor] .
         endfm",
        false,
    );
    assert!(!entered.exit, "{}", entered.output);
    assert_eq!(session.current(), Some("CYCLE-BASE"));

    let cases = [
        // Direct self-loop.
        ("CYCLE-SELF", "sort S . subsort S < S ."),
        // Two-sort cycle in one declaration chain.
        ("CYCLE-CHAIN", "sorts S T . subsorts S < T < S ."),
        // Longer cycle across separate declarations.
        (
            "CYCLE-LONG",
            "sorts P Q R . subsort P < Q . subsort Q < R . subsort R < P .",
        ),
        // Cycle that only appears after flattening the import of CYCLE-BASE (A < B).
        ("CYCLE-IMPORT", "including CYCLE-BASE . subsort B < A ."),
    ];
    for (name, body) in cases {
        let out = session.eval(&format!("fmod {name} is {body} endfm"), false);
        assert!(!out.exit, "{}", out.output);
        assert!(
            out.output.starts_with("error:") && out.output.contains(name),
            "{name}: expected a declaration diagnostic, got {:?}",
            out.output
        );
        assert!(out.output.contains("cycle"), "{}", out.output);
        assert_eq!(session.current(), Some("CYCLE-BASE"), "{name} was selected");

        let shown = session.eval(&format!("show module {name} ."), false);
        assert!(
            shown.output.starts_with("error:") && shown.output.contains("no such module"),
            "{name} was installed: {}",
            shown.output
        );
    }

    // A rejected redefinition leaves the prior definition in place.
    let redefined = session.eval(
        "fmod CYCLE-BASE is sorts A B . subsort A < B . subsort B < A . op a : -> A . endfm",
        false,
    );
    assert!(
        redefined.output.starts_with("error:"),
        "{}",
        redefined.output
    );
    let base = session.eval("reduce in CYCLE-BASE : a .", false);
    assert!(base.output.contains("result A: a"), "{}", base.output);

    // The Session keeps working for new valid modules in the same and later submissions.
    let later = session.eval(
        "fmod CYCLE-BAD is sorts X Y . subsort X < Y . subsort Y < X . endfm
         fmod CYCLE-AFTER is sort D . op d : -> D . endfm
         reduce d .",
        false,
    );
    assert!(later.output.starts_with("error:"), "{}", later.output);
    assert!(later.output.contains("result D: d"), "{}", later.output);
    assert_eq!(session.current(), Some("CYCLE-AFTER"));
}

/// Manual §16.1: each `CounterSymbol` operator has its own `0, 1, 2, ...` sequence. All of them
/// restart for each top-level `rewrite`/`frewrite`/`erewrite` and keep their values across
/// `continue`. Covers a renamed copy of one counter and two counters declared directly.
#[test]
fn counter_operators_keep_independent_sequences() {
    let mut session = Session::new();
    let entered = session.eval(
        "fmod PEANO is
           sorts Zero NzNat Nat .
           subsorts Zero NzNat < Nat .
           op 0 : -> Zero [ctor] .
           op s_ : Nat -> NzNat [ctor iter special (id-hook SuccSymbol term-hook zeroTerm (0))] .
         endfm
         mod TICKER is
           protecting PEANO .
           op tick : -> [Nat] [special (id-hook CounterSymbol op-hook succSymbol (s_ : Nat ~> NzNat))] .
         endm
         mod RENAMED-PAIR is
           including TICKER .
           including TICKER * (op tick to tock) .
           sort Seq .
           subsort Nat < Seq .
           op _;_ : Seq Seq -> Seq [assoc] .
         endm
         mod DIRECT-PAIR is
           protecting PEANO .
           op up : -> [Nat] [special (id-hook CounterSymbol op-hook succSymbol (s_ : Nat ~> NzNat))] .
           op dn : -> [Nat] [special (id-hook CounterSymbol op-hook succSymbol (s_ : Nat ~> NzNat))] .
           sort Seq .
           subsort Nat < Seq .
           op _;_ : Seq Seq -> Seq [assoc] .
         endm",
        false,
    );
    assert!(!entered.exit);
    assert_eq!(entered.output, "");

    let mut expect = |command: &str, expected: &str| {
        let out = session.eval(command, false);
        assert!(!out.exit);
        assert!(
            out.output.trim_end().ends_with(expected),
            "{command}\nexpected suffix:\n{expected}\ngot:\n{}",
            out.output
        );
    };
    expect("select RENAMED-PAIR .", "");
    expect(
        "rewrite tick ; tock ; tick ; tock .",
        "rewrites: 4\nresult Seq: 0 ; 0 ; 1 ; 1",
    );
    // A fresh command restarts both counters.
    expect(
        "rewrite tock ; tock ; tick .",
        "rewrites: 3\nresult Seq: 0 ; 1 ; 0",
    );
    expect(
        "frewrite tick ; tock ; tick ; tock .",
        "rewrites: 4\nresult Seq: 0 ; 0 ; 1 ; 1",
    );
    expect(
        "erewrite tock ; tick ; tock .",
        "rewrites: 3\nresult Seq: 0 ; 0 ; 1",
    );
    expect(
        "rewrite [2] tick ; tock ; tick ; tock .",
        "rewrites: 2\nresult [Seq]: 0 ; 0 ; tick ; tock",
    );
    // `continue` resumes each counter where the bounded run left it.
    expect("continue .", "rewrites: 2\nresult Seq: 0 ; 0 ; 1 ; 1");

    expect("select DIRECT-PAIR .", "");
    expect(
        "rewrite up ; dn ; up ; dn .",
        "rewrites: 4\nresult Seq: 0 ; 0 ; 1 ; 1",
    );
    expect(
        "frewrite dn ; dn ; up .",
        "rewrites: 3\nresult Seq: 0 ; 1 ; 0",
    );
}

/// A Session with the META-LEVEL prelude loaded.
fn meta_session() -> Session {
    let mut session = Session::new();
    let prelude = session.eval(
        include_str!("../../../conformance/prelude-meta.maude"),
        false,
    );
    assert!(
        !prelude.output.contains("error in module") && !prelude.output.contains("parse error"),
        "META-LEVEL prelude: {}",
        prelude.output
    );
    session
}

/// `metaXapply` and `metaXmatch` treat the copies of a repeated element of an associative-commutative
/// subterm as one position, so a reflected rewrite or match is reported once rather than once per copy.
/// Enumerating solution indices until failure therefore counts each one-step rewrite once. The two
/// arguments of a commutative operator remain two positions with distinct contexts.
#[test]
fn meta_xapply_and_xmatch_visit_a_repeated_ac_element_once() {
    let mut session = meta_session();
    let modules = session.eval(
        "mod XPOS is
           sorts Coin Item Marking .
           subsorts Coin Item < Marking .
           op __ : Marking Marking -> Marking [ctor assoc comm] .
           ops d e : -> Coin [ctor] .
           ops c f : -> Item [ctor] .
           op k : Marking -> Marking [ctor] .
           op pair : Marking Marking -> Marking [ctor comm] .
           rl [b] : d => c .
           rl [b] : e => f .
         endm
         fmod XPOS-COUNT is
           protecting META-LEVEL .
           op count : Term Nat -> Nat .
           var T : Term .
           var N : Nat .
           eq count(T, N)
            = if metaXapply(upModule('XPOS, false), T, 'b, none, 0, unbounded, N)
                 == (failure).Result4Tuple?
              then N else count(T, s N) fi .
         endfm",
        false,
    );
    assert!(!modules.output.contains("error"), "{}", modules.output);

    let out = session
        .eval(
            "red in META-LEVEL : metaXapply(upModule('XPOS, false), '__['d.Coin, 'd.Coin, 'd.Coin], 'b, none, 0, unbounded, 0) .
             red in META-LEVEL : metaXapply(upModule('XPOS, false), '__['d.Coin, 'd.Coin, 'd.Coin], 'b, none, 0, unbounded, 1) .
             red in META-LEVEL : metaXmatch(upModule('XPOS, false), 'd.Coin, '__['d.Coin, 'd.Coin, 'd.Coin], nil, 0, unbounded, 0) .
             red in META-LEVEL : metaXmatch(upModule('XPOS, false), 'd.Coin, '__['d.Coin, 'd.Coin, 'd.Coin], nil, 0, unbounded, 1) .
             red in META-LEVEL : metaXapply(upModule('XPOS, false), '__['k['d.Coin], 'k['d.Coin], 'k['d.Coin]], 'b, none, 0, unbounded, 0) .
             red in META-LEVEL : metaXapply(upModule('XPOS, false), '__['k['d.Coin], 'k['d.Coin], 'k['d.Coin]], 'b, none, 0, unbounded, 1) .
             red in META-LEVEL : metaXapply(upModule('XPOS, false), 'pair['d.Coin, 'd.Coin], 'b, none, 0, unbounded, 0) .
             red in META-LEVEL : metaXapply(upModule('XPOS, false), 'pair['d.Coin, 'd.Coin], 'b, none, 0, unbounded, 1) .
             red in META-LEVEL : metaXapply(upModule('XPOS, false), 'pair['d.Coin, 'd.Coin], 'b, none, 0, unbounded, 2) .
             red in XPOS-COUNT : count('__['d.Coin, 'd.Coin, 'd.Coin], 0) .
             red in XPOS-COUNT : count('__['d.Coin, 'e.Coin, 'd.Coin, 'd.Coin], 0) .",
            false,
        )
        .output;
    let results: Vec<&str> = out
        .lines()
        .filter(|line| line.starts_with("result "))
        .collect();
    assert_eq!(
        results,
        vec![
            // `d d d` has one `d => c` redex modulo AC; index 1 is past the last solution.
            "result Result4Tuple: {'__['d.Coin, 'd.Coin, 'c.Item], 'Marking, (none).Substitution, '__['d.Coin, 'd.Coin, []]}",
            "result Result4Tuple?: (failure).Result4Tuple?",
            "result MatchPair: {(none).Substitution, '__['d.Coin, 'd.Coin, []]}",
            "result MatchPair?: (noMatch).MatchPair?",
            // A repeated non-constant element is also one position, together with its subterms.
            "result Result4Tuple: {'__['k['d.Coin], 'k['d.Coin], 'k['c.Item]], 'Marking, (none).Substitution, '__['k[[]], 'k['d.Coin], 'k['d.Coin]]}",
            "result Result4Tuple?: (failure).Result4Tuple?",
            // Equal arguments of a commutative, non-associative operator stay two positions.
            "result Result4Tuple: {'pair['d.Coin, 'c.Item], 'Marking, (none).Substitution, 'pair[[], 'd.Coin]}",
            "result Result4Tuple: {'pair['d.Coin, 'c.Item], 'Marking, (none).Substitution, 'pair['d.Coin, []]}",
            "result Result4Tuple?: (failure).Result4Tuple?",
            // One rewrite of `d`, and one rewrite each of `d` and `e`.
            "result NzNat: 1",
            "result NzNat: 2",
        ],
        "{out}"
    );
}

/// A rule step below an `iter` node keeps the node's count at the metalevel and for the prelude's
/// `Nat` successor. `s_^3(a)` denotes `s(s(s(a)))`, so with `rl a => b` the reflected one-step and
/// normal-form results are `'s_^3['b.S]`. The hole of a `metaXapply`, `metaXmatch`, or
/// `metaNarrowingApply` context below the tower sits under three applications, `'s_^3[[]]`, so
/// filling it with the redex rebuilds the subject. With `rl a => 0` in `Nat`, `s_^3(a)` rewrites to
/// `3`, not `1`.
#[test]
fn rule_steps_below_iter_keep_the_count_through_meta_and_nat() {
    let mut session = meta_session();
    let modules = session.eval(
        "mod ITER-META is
           sort S .
           ops a b : -> S .
           op s_ : S -> S [iter] .
           op h : S S -> S .
           op f : S -> S .
           rl [r] : a => b .
           rl [n] : f(X:S) => X:S [narrowing] .
         endm
         mod ITER-NAT is
           protecting NAT .
           op a : -> Nat .
           rl [r] : a => 0 .
         endm",
        false,
    );
    assert!(!modules.output.contains("error"), "{}", modules.output);

    let out = session
        .eval(
            "rew in ITER-NAT : s_^3(a) .
             frew in ITER-NAT : s_^3(a) .
             red in META-LEVEL : metaRewrite(upModule('ITER-META, false), 's_^3['a.S], unbounded) .
             red in META-LEVEL : metaFrewrite(upModule('ITER-META, false), 's_^3['a.S], unbounded, 1) .
             red in META-LEVEL : metaSearch(upModule('ITER-META, false), 's_^3['a.S], 's_^3['b.S], nil, '+, unbounded, 0) .
             red in META-LEVEL : metaXapply(upModule('ITER-META, false), 's_^3['a.S], 'r, none, 0, unbounded, 0) .
             red in META-LEVEL : metaXapply(upModule('ITER-META, false), 'h['s_^3['a.S], 'b.S], 'r, none, 0, unbounded, 0) .
             red in META-LEVEL : metaXmatch(upModule('ITER-META, false), 'a.S, 's_^3['a.S], nil, 0, unbounded, 0) .",
            false,
        )
        .output;
    let results: Vec<&str> = out
        .lines()
        .filter(|line| line.starts_with("result "))
        .collect();
    assert_eq!(
        results,
        vec![
            "result NzNat: 3",
            "result NzNat: 3",
            "result ResultPair: {'s_^3['b.S], 'S}",
            "result ResultPair: {'s_^3['b.S], 'S}",
            "result ResultTriple: {'s_^3['b.S], 'S, (none).Substitution}",
            "result Result4Tuple: {'s_^3['b.S], 'S, (none).Substitution, 's_^3[[]]}",
            "result Result4Tuple: {'h['s_^3['b.S], 'b.S], 'S, (none).Substitution, 'h['s_^3[[]], 'b.S]}",
            "result MatchPair: {(none).Substitution, 's_^3[[]]}",
        ],
        "{out}"
    );

    // Narrowing already rebuilt the term with its count; its context now agrees with it.
    let narrowed = session
        .eval(
            "red in META-LEVEL : metaNarrowingApply(upModule('ITER-META, false), 's_^3['f['Y:S]], empty, '#, 0) .",
            false,
        )
        .output;
    assert!(
        narrowed.contains("'s_^3['@1:S], 'S,\n  's_^3[[]],\n  'n,"),
        "{narrowed}"
    );
}

/// The model checker explores the successors of a state through the same rule-position splice as
/// search, so a rule step below an `iter` node keeps the node's count there too. From `s_^3(a)` with
/// `rl a => b` the only successor is `s_^3(b)`, where `atB` holds: `<> atB` is true and `[] ~ atB`
/// fails at that state.
#[test]
fn model_checking_keeps_the_count_of_an_iter_state() {
    let mut session = meta_session();
    let checker = session.eval(
        include_str!("../../../share/maude-gpl/model-checker.maude"),
        false,
    );
    assert!(
        !checker.output.contains("error in module") && !checker.output.contains("parse error"),
        "{}",
        checker.output
    );
    let module = session.eval(
        "mod ITER-LTL is
           including MODEL-CHECKER .
           sort S .
           subsort S < State .
           ops a b : -> S .
           op s_ : S -> S [iter] .
           op atB : -> Prop .
           rl [r] : a => b .
           eq s_^3(b) |= atB = true .
           eq X:S |= P:Prop = false [owise] .
         endm",
        false,
    );
    assert!(!module.output.contains("error"), "{}", module.output);

    let out = session
        .eval(
            "red modelCheck(s_^3(a), <> atB) .
             red modelCheck(s_^3(a), [] ~ atB) .",
            false,
        )
        .output;
    let results: Vec<&str> = out
        .lines()
        .filter(|line| line.starts_with("result "))
        .collect();
    assert_eq!(
        results,
        vec![
            "result Bool: true",
            "result ModelCheckResult: counterexample({s_^3(a), 'r}, {s_^3(b), deadlock})",
        ],
        "{out}"
    );
}

/// The `state:` lines of a narrowing command's output, in order.
fn narrowing_states(output: &str) -> Vec<&str> {
    output
        .lines()
        .filter_map(|line| line.strip_prefix("state: "))
        .collect()
}

/// Narrowing explores both arguments of a free, associative, or non-commutative identity operator
/// even when they are one shared node, as after instantiating `pr(Y, Y)` or in a ground subject
/// `pr(g(a), g(a))`. Those steps were skipped while exhaustion was still reported complete. Two
/// arguments of a commutative operator that are one shared node are narrowed once, because both
/// choices give states equal modulo commutativity. A repeated element of an associative-commutative
/// operator is one position.
#[test]
fn narrowing_explores_shared_arguments_of_non_commutative_operators() {
    let mut session = Session::new();
    let module = session.eval(
        "mod NARROW-SHARED is
           sort T .
           ops a c e : -> T [ctor] .
           op g : T -> T [ctor] .
           op pr : T T -> T [ctor] .
           op _;_ : T T -> T [ctor assoc] .
           op un : T T -> T [ctor id: e] .
           op sw : T T -> T [ctor comm] .
           op __ : T T -> T [ctor assoc comm] .
           ops dup seq unit swap bag : T -> T [ctor] .
           var Y : T .
           rl [dup] : dup(Y) => pr(Y, Y) [narrowing] .
           rl [seq] : seq(Y) => Y ; Y [narrowing] .
           rl [unit] : unit(Y) => un(Y, Y) [narrowing] .
           rl [swap] : swap(Y) => sw(Y, Y) [narrowing] .
           rl [bag] : bag(Y) => Y Y [narrowing] .
           rl [ga] : g(a) => c [narrowing] .
         endm",
        false,
    );
    assert!(
        !module.output.contains("error") && !module.output.contains("warning"),
        "{}",
        module.output
    );

    // The rule instance shares `g(@1)` between both arguments; the goal needs the second one narrowed.
    for (command, state) in [
        ("vu-narrow dup(g(X:T)) =>* pr(g(a), c) .", "pr(g(a), c)"),
        ("vu-narrow seq(g(X:T)) =>* g(a) ; c .", "g(a) ; c"),
        ("vu-narrow unit(g(X:T)) =>* un(g(a), c) .", "un(g(a), c)"),
    ] {
        let out = session.eval(command, false).output;
        assert_eq!(narrowing_states(&out), vec![state], "{command}\n{out}");
        assert!(out.contains("X:T --> a"), "{command}\n{out}");
    }

    // A ground subject is built with its equal subterms shared; both are still narrowed, as in search.
    let ground = session
        .eval("vu-narrow pr(g(a), g(a)) =>1 Z:T .", false)
        .output;
    assert_eq!(
        narrowing_states(&ground),
        vec!["pr(c, g(a))", "pr(g(a), c)"],
        "{ground}"
    );

    // Commutative pairs keep their behavior: one shared node is narrowed once, while separately built
    // equal arguments are both narrowed.
    let shared_comm = session
        .eval("vu-narrow [, 2] swap(g(X:T)) =>+ Z:T .", false)
        .output;
    let states = narrowing_states(&shared_comm);
    assert_eq!(states.len(), 4, "{shared_comm}");
    assert_eq!(
        states[1..],
        ["swap(c)", "sw(c, g(a))", "sw(c, c)"],
        "{shared_comm}"
    );
    let separate_comm = session
        .eval("vu-narrow sw(g(X:T), g(X:T)) =>1 Z:T .", false)
        .output;
    assert_eq!(
        narrowing_states(&separate_comm),
        vec!["sw(c, g(a))", "sw(g(a), c)"],
        "{separate_comm}"
    );

    // The two copies of `g(@1)` in an associative-commutative instance are one position.
    let bag = session
        .eval("vu-narrow [, 2] bag(g(X:T)) =>+ Z:T .", false)
        .output;
    let states = narrowing_states(&bag);
    assert_eq!(states.len(), 4, "{bag}");
    assert_eq!(states[1..], ["bag(c)", "c g(a)", "c c"], "{bag}");
}

/// Reflected narrowing shares the object-level position enumeration: the state reachable only through
/// the second argument of a shared rule instance is found by `metaNarrowingSearch`.
#[test]
fn meta_narrowing_search_explores_shared_arguments() {
    let mut session = meta_session();
    let module = session.eval(
        "mod NARROW-META is
           sort T .
           ops a c : -> T [ctor] .
           op g : T -> T [ctor] .
           op pr : T T -> T [ctor] .
           op dup : T -> T [ctor] .
           var Y : T .
           rl [dup] : dup(Y) => pr(Y, Y) [narrowing] .
           rl [ga] : g(a) => c [narrowing] .
         endm",
        false,
    );
    assert!(!module.output.contains("error"), "{}", module.output);
    let out = session
        .eval(
            "red in META-LEVEL : metaNarrowingSearch(upModule('NARROW-META, false), 'dup['g['X:T]], 'pr['g['a.T], 'c.T], '*, unbounded, 'none, 0) .",
            false,
        )
        .output;
    assert!(out.contains("result NarrowingSearchResult:"), "{out}");
    assert!(out.contains("'pr['g['a.T], 'c.T], 'T,"), "{out}");
    assert!(out.contains("'X:T <- 'a.T"), "{out}");
}

/// A self-contained SMT signature and one conditional rule for SMT-search tests. `opaque` has an SMT
/// sort but no SMT hook, so a configured backend cannot translate a formula containing it (`BadDag`).
const SMT_CELL_MODULES: &str = "fmod CELL-SMT is
       sorts Prop Num .
       op true : -> Prop [special (id-hook SMT_Symbol (true))] .
       op _and_ : Prop Prop -> Prop [prec 55 special (id-hook SMT_Symbol (and))] .
       op _===_ : Num Num -> Prop [prec 51 special (id-hook SMT_Symbol (===))] .
       op _<_ : Num Num -> Prop [prec 37 special (id-hook SMT_Symbol (<))] .
       op _+_ : Num Num -> Num [prec 33 special (id-hook SMT_Symbol (+))] .
       op <Nums> : -> Num [special (id-hook SMT_NumberSymbol (integers))] .
     endfm
     mod CELL is
       pr CELL-SMT .
       sort Cell .
       op cell : Num -> Cell .
       op opaque : Num -> Num .
       vars N M : Num .
       var C : Cell .
       crl cell(N) => cell(N + 1) if N < 2 = true .
     endm";

/// An `=>*` initial state that matches the goal is a solution only when the backend returns `Sat` for
/// the `such that` constraint, as for every other retained match. This also holds when the goal has
/// no SMT variable of its own to constrain. The null backend answers `Unknown`, so in the default
/// profile only the unconstrained search reports its initial state.
#[test]
fn smt_search_initial_state_needs_a_satisfiable_constraint() {
    let mut session = Session::new();
    let modules = session.eval(SMT_CELL_MODULES, false);
    assert!(
        !modules.output.contains("error") && !modules.output.contains("warning"),
        "{}",
        modules.output
    );

    for command in [
        // Unsatisfiable.
        "smt-search [2] cell(N) =>* C such that N = N + 1 .",
        // `BadDag` for a configured backend. The goal's own match constraint `M === N` translates,
        // so only the check of the initial constraint rejects this match.
        "smt-search [2] cell(N) =>* cell(M) such that opaque(N) = M .",
    ] {
        let out = session.eval(command, false).output;
        assert!(
            out.contains("No solution.") && !out.contains("Solution 1"),
            "{command}\n{out}"
        );
    }

    let satisfiable = session
        .eval("smt-search [2] cell(N) =>* C such that N = 5 .", false)
        .output;
    if cfg!(feature = "smt-z3") {
        assert!(
            satisfiable.contains(
                "Solution 1\nrewrites: 0\nstate: cell(N)\nC --> cell(N)\nwhere N === 5\n"
            ),
            "{satisfiable}"
        );
    } else {
        assert!(
            satisfiable.contains("No solution.") && !satisfiable.contains("Solution 1"),
            "{satisfiable}"
        );
    }

    // In the default profile this pins current behavior, not a contract: the null backend answers
    // `Unknown` for the literal `true` constraint as well, yet the unconstrained initial state is
    // still reported. Whether a trivial constraint needs a backend `Sat` is undecided (TNK-DEV-012).
    let unconstrained = session.eval("smt-search [2] cell(0) =>* C .", false).output;
    assert!(
        unconstrained
            .contains("Solution 1\nrewrites: 0\nstate: cell(0)\nC --> cell(0)\nwhere true\n"),
        "{unconstrained}"
    );
}

/// `metaSmtSearch` follows the same rule: solution 0 of an `'*` search is `failure` when the backend
/// does not return `Sat` for the initial constraint.
#[test]
fn meta_smt_search_initial_state_needs_a_satisfiable_constraint() {
    let mut session = meta_session();
    let modules = session.eval(
        &format!("set include BOOL off .\n{SMT_CELL_MODULES}"),
        false,
    );
    assert!(
        !modules.output.contains("error") && !modules.output.contains("warning"),
        "{}",
        modules.output
    );
    let out = session
        .eval(
            "red in META-LEVEL : metaSmtSearch(upModule('CELL, false), 'cell['N:Num], 'C:Cell, 'N:Num = '_+_['N:Num, '1.Num], '*, 0, unbounded, 0) .
             red in META-LEVEL : metaSmtSearch(upModule('CELL, false), 'cell['N:Num], 'cell['M:Num], 'opaque['N:Num] = 'M:Num, '*, 0, unbounded, 0) .
             red in META-LEVEL : metaSmtSearch(upModule('CELL, false), 'cell['N:Num], 'C:Cell, 'N:Num = '5.Num, '*, 0, unbounded, 0) .",
            false,
        )
        .output;
    let results: Vec<&str> = out
        .lines()
        .filter(|line| line.starts_with("result "))
        .collect();
    let failure = "result SmtResult?: (failure).SmtResult?";
    assert_eq!(results.len(), 3, "{out}");
    assert_eq!(results[..2], [failure, failure], "{out}");
    if cfg!(feature = "smt-z3") {
        // The prelude's `_<-_` format puts the assignment on its own line.
        assert!(
            results[2].starts_with("result SmtResult: {'cell['N:Num],")
                && out.contains("'C:Cell <- 'cell['N:Num], '_===_['N:Num, '5.Num], 0}"),
            "{out}"
        );
    } else {
        assert_eq!(results[2], failure, "{out}");
    }
}

// `ops`/`msgs` declare one operator per top-level parenthesized group, so grouped constants,
// mixfix names, and parameterized constants are usable and instantiate through a view.
#[test]
fn ops_and_msgs_declare_one_operator_per_parenthesized_group() {
    let mut session = Session::new();
    let plain = session.eval(
        "fmod OPS-GROUP is
           sort Bar .
           ops (m{X}) (n{X}) (p{X,X}) : -> Bar .
           ops ([_]) (<_>) : Bar -> Bar .
           op f : Bar -> Bar .
           eq f(m{X}) = n{X} .
           eq f(n{X}) = p{X,X} .
           eq [ m{X} ] = < n{X} > .
         endfm
         reduce f(f(m{X})) .
         reduce [ m{X} ] .",
        false,
    );
    assert!(!plain.output.contains("warning"), "{}", plain.output);
    assert!(!plain.output.contains("error"), "{}", plain.output);
    assert!(plain.output.contains("result Bar: p{X"), "{}", plain.output);
    assert!(
        plain.output.contains("result Bar: < n{X} >"),
        "{}",
        plain.output
    );

    let messages = session.eval(
        "omod MSGS-GROUP is
           msgs (to_hi) (ack{X}) : Oid -> Msg .
           op o : -> Oid .
         endom
         reduce to o hi .
         reduce ack{X}(o) .",
        false,
    );
    assert!(!messages.output.contains("error"), "{}", messages.output);
    assert!(
        messages.output.contains("result Msg: to o hi"),
        "{}",
        messages.output
    );
    assert!(
        messages.output.contains("result Msg: ack{X}(o)"),
        "{}",
        messages.output
    );

    let instantiated = session.eval(
        "fth OPS-T is
           sort Elt .
           ops (e1) (e2) : -> Elt [pconst] .
         endfth
         fmod OPS-N is
           sort N .
           ops z1 z2 : -> N .
         endfm
         view OpsV from OPS-T to OPS-N is
           sort Elt to N .
           op e1 to z1 .
           op e2 to z2 .
         endv
         fmod OPS-P{X :: OPS-T} is
           sort Bar{X} .
           ops (m{X}) (n{X}) : -> Bar{X} .
           op f : Bar{X} -> Bar{X} .
           op g : X$Elt -> X$Elt .
           eq f(m{X}) = n{X} .
           eq g(X$e1) = X$e2 .
         endfm
         fmod OPS-USE is
           including OPS-P{OpsV} .
         endfm
         reduce f(m{OpsV}) .
         reduce g(z1) .",
        false,
    );
    assert!(
        !instantiated.output.contains("error"),
        "{}",
        instantiated.output
    );
    assert!(
        instantiated.output.contains("result Bar{OpsV}: n{OpsV}"),
        "{}",
        instantiated.output
    );
    assert!(
        instantiated.output.contains("result N: z2"),
        "{}",
        instantiated.output
    );
}

// Renaming a parameterized class (`class Foo{X} to Bar{X}`) or message (`msg m{X} to n{X}`) is a
// structured renaming item: the importer builds, and the instance sees only the renamed names.
#[test]
fn structured_class_and_message_renamings_instantiate() {
    let mut session = Session::new();
    let out = session.eval(
        "fth REN-T is
           sort Elt .
         endfth
         fmod REN-N is
           sort N .
         endfm
         view RenV from REN-T to REN-N is
           sort Elt to N .
         endv
         omod REN-FOO{X :: REN-T} is
           class Foo{X} .
           msg m{X} : Oid -> Msg .
         endom
         omod REN-BAR{X :: REN-T} is
           including REN-FOO{X} * (class Foo{X} to Bar{X}, msg m{X} to n{X}) .
           op className : -> Cid .
           eq className = Bar{X} .
         endom
         omod REN-TEST is
           including REN-BAR{RenV} .
           op o : -> Oid .
         endom
         reduce className .
         reduce n{RenV}(o) .
         reduce m{RenV}(o) .",
        false,
    );
    assert!(!out.output.contains("parse error"), "{}", out.output);
    assert!(
        out.output.contains("result Bar{RenV}: Bar{RenV}"),
        "{}",
        out.output
    );
    assert!(
        out.output.contains("result Msg: n{RenV}(o)"),
        "{}",
        out.output
    );
    // The source message name is gone from the renamed instance.
    assert!(
        out.output.contains("error: no parse at token 0 (`m`)"),
        "{}",
        out.output
    );
}

// The documented class qualifier `attr a . C to b` parses in renamings and view maps, including a
// structured class. Attribute operators are shared by name across classes, so the qualifier does
// not narrow the map: the same-named attribute of another class is renamed too.
#[test]
fn class_qualified_attribute_maps_parse_in_renamings_and_views() {
    let mut session = Session::new();
    let renamed = session.eval(
        "omod ATTR-A is
           sort V .
           op v : -> V .
           class C | x : V .
           class D | x : V .
           op o : -> Oid .
         endom
         omod ATTR-B is
           including ATTR-A * (attr x . C to y) .
         endom
         reduce in ATTR-B : < o : C | y : v > .
         reduce in ATTR-B : < o : D | y : v > .
         oth ATTR-T is
           sort W .
           class E | z : W .
         endoth
         view AttrV from ATTR-T to ATTR-A is
           sort W to V .
           class E to C .
           attr z . E to x .
         endv",
        false,
    );
    assert!(!renamed.output.contains("error"), "{}", renamed.output);
    assert!(
        renamed.output.contains("result Object: < o : C | y : v >"),
        "{}",
        renamed.output
    );
    assert!(
        renamed.output.contains("result Object: < o : D | y : v >"),
        "{}",
        renamed.output
    );

    let structured = session.eval(
        "fth ATTR-TRIV is
           sort Elt .
         endfth
         fmod ATTR-N is
           sort N .
         endfm
         view AttrN from ATTR-TRIV to ATTR-N is
           sort Elt to N .
         endv
         omod ATTR-P{X :: ATTR-TRIV} is
           sort U .
           op u : -> U .
           class Buf{X} | contents : U .
         endom
         omod ATTR-Q{X :: ATTR-TRIV} is
           including ATTR-P{X} * (attr contents . Buf{X} to items) .
         endom
         omod ATTR-R is
           including ATTR-Q{AttrN} .
           op o : -> Oid .
         endom
         reduce < o : Buf{AttrN} | items : u > .",
        false,
    );
    assert!(
        !structured.output.contains("error"),
        "{}",
        structured.output
    );
    assert!(
        structured
            .output
            .contains("result Object: < o : Buf{AttrN} | items : u >"),
        "{}",
        structured.output
    );
}

/// A minimal truth-value module; its `true` anchors bare Boolean condition fragments.
const TRUTH_MIN: &str = "fmod TRUTH-MIN is
  sort Bool .
  op true : -> Bool [ctor special (id-hook SystemTrue)] .
  op false : -> Bool [ctor special (id-hook SystemFalse)] .
endfm
";

/// Assert that every expected line occurs in `output`.
fn assert_lines(output: &str, expected: &[&str]) {
    for line in expected {
        assert!(output.contains(line), "missing {line:?} in:\n{output}");
    }
}

// Operator names may contain connective text (`<_:_>`, object syntax), so a condition fragment is
// not split at its first `:`. Every fragment form over such terms executes, in statements, a search
// condition, and object-module rules (object completion then applies to the retained rules).
#[test]
fn condition_fragments_may_contain_mixfix_colons() {
    let mut session = Session::new();
    let source = format!(
        "{TRUTH_MIN}
         mod COND-COLON is
           protecting TRUTH-MIN .
           sorts S S2 T .
           subsort S2 < S .
           op <_:_> : S T -> S [ctor] .
           op _~_ : S S -> Bool .
           ops a b c d e : -> S [ctor] .
           op t : -> T [ctor] .
           ops f g h n p : S -> S .
           eq X:S ~ X:S = true .
           crl [r1] : a => b if < a : t > = < a : t > .
           ceq f(X:S) = b if < X:S : t > = < a : t > .
           ceq g(X:S) = Y:S if < Y:S : t > := < X:S : t > .
           crl [r2] : c => d if < c : t > => < Z:S : t > .
           ceq h(X:S) = b if < X:S : t > : S .
           ceq n(X:S) = b if < X:S : t > ~ < a : t > .
           cmb p(X:S) : S2 if < X:S : t > = < e : t > .
           rl [r3] : < a : t > => < b : t > .
         endm
         rewrite [1] a .
         reduce f(a) .
         reduce g(a) .
         rewrite [1] c .
         reduce h(a) .
         reduce n(a) .
         reduce n(c) .
         reduce p(e) .
         search < a : t > =>* < X:S : t > such that < X:S : t > = < b : t > ."
    );
    let plain = session.eval(&source, false);
    assert!(!plain.output.contains("warning"), "{}", plain.output);
    assert!(!plain.output.contains("error"), "{}", plain.output);
    assert_lines(
        &plain.output,
        &[
            "rewrite [1] in COND-COLON : a .\nrewrites: 1\nresult S: b",
            "reduce in COND-COLON : f(a) .\nrewrites: 1\nresult S: b",
            "reduce in COND-COLON : g(a) .\nrewrites: 1\nresult S: a",
            "rewrite [1] in COND-COLON : c .\nrewrites: 1\nresult S: d",
            "reduce in COND-COLON : h(a) .\nrewrites: 1\nresult S: b",
            "reduce in COND-COLON : n(a) .\nrewrites: 2\nresult S: b",
            "reduce in COND-COLON : n(c) .\nrewrites: 0\nresult S: n(c)",
            "result S2: p(e)",
            "X:S --> b",
        ],
    );

    let objects = session.eval(
        "set verbose on .
         omod COND-OBJ is
           protecting TRUTH-MIN .
           sort Val .
           ops v0 v1 v2 : -> Val [ctor] .
           op next : Val -> Val .
           eq next(v0) = v1 .
           eq next(v1) = v2 .
           class Cell | val : Val .
           op c1 : -> Oid [ctor] .
           ops bump copy : Oid -> Msg [ctor] .
           var O : Oid .
           vars V W : Val .
           crl [bump] : bump(O) < O : Cell | val : V > => < O : Cell | val : next(V) >
             if < O : Cell | val : V > = < O : Cell | val : v0 > .
           crl [copy] : copy(O) < O : Cell | val : V > => < O : Cell | val : W >
             if < O : Cell | val : W > := < O : Cell | val : next(V) > .
         endom
         set verbose off .
         rewrite bump(c1) < c1 : Cell | val : v0 > .
         rewrite bump(c1) < c1 : Cell | val : v1 > .
         rewrite copy(c1) < c1 : Cell | val : v1 > .",
        false,
    );
    assert!(!objects.output.contains("warning"), "{}", objects.output);
    assert!(!objects.output.contains("error"), "{}", objects.output);
    // The retained rule reaches object completion.
    assert!(
        objects.output.contains("Transformed rule:\n  crl [bump] :"),
        "{}",
        objects.output
    );
    assert_lines(
        &objects.output,
        &[
            "result Object: < c1 : Cell | val : v1 >",
            "result Configuration: bump(c1) < c1 : Cell | val : v1 >",
            "result Object: < c1 : Cell | val : v2 >",
        ],
    );
}

// A membership's delimiter is the colon before its target sort, so subjects may contain colons
// (a user `<_:_>`, a `: t [ a ]` subterm, object syntax). An unknown target sort is reported as such.
#[test]
fn membership_subjects_may_contain_mixfix_colons() {
    let mut session = Session::new();
    let plain = session.eval(
        "fmod MB-COLON is
           sorts S S2 T .
           subsort S2 < S .
           op <_:_> : S T -> S [ctor] .
           op _[_] : T S -> T [ctor] .
           ops a e : -> S [ctor] .
           op t : -> T [ctor] .
           mb < e : t > : S2 .
           cmb < X:S : t > : S2 if X:S = a .
           mb [bracket] : < e : t [ a ] > : S2 .
           mb < a : t > : Nope .
         endfm
         reduce < e : t > .
         reduce < a : t > .
         reduce < e : t [ a ] > .
         reduce < e : t [ e ] > .",
        false,
    );
    assert!(!plain.output.contains("error"), "{}", plain.output);
    assert_eq!(
        plain.output.matches("warning").count(),
        1,
        "{}",
        plain.output
    );
    assert_lines(
        &plain.output,
        &[
            "dropped membership: unknown sort `Nope`",
            "result S2: < e : t >",
            "result S2: < a : t >",
            "result S2: < e : t[a] >",
            "result S: < e : t[e] >",
        ],
    );

    let objects = session.eval(
        "omod MB-OBJ is
           sorts Val GoodObj .
           subsort GoodObj < Object .
           ops v w : -> Val [ctor] .
           op o : -> Oid [ctor] .
           class Cell | val : Val .
           var O : Oid .
           var V : Val .
           mb < O : Cell | val : v > : GoodObj .
           cmb < O : Cell | val : V > : GoodObj if V = w [label cw] .
         endom
         reduce < o : Cell | val : v > .
         reduce < o : Cell | val : w > .",
        false,
    );
    assert!(!objects.output.contains("warning"), "{}", objects.output);
    assert_lines(
        &objects.output,
        &[
            "result GoodObj: < o : Cell | val : v >",
            "result GoodObj: < o : Cell | val : w >",
        ],
    );
}

// `if` is not reserved: the `ceq`/`crl` condition keyword is the first top-level `if` that no later
// top-level `fi` closes, so `if_then_else_fi` may stand unparenthesized on either side of the
// statement or in its condition.
#[test]
fn if_then_else_fi_may_stand_beside_the_condition_keyword() {
    let mut session = Session::new();
    let equations = session.eval(
        "fmod ITE is
           sorts Bool S .
           ops true false : -> Bool [ctor] .
           ops a b c : -> S [ctor] .
           op if_then_else_fi : Bool S S -> S .
           op if_then_else_fi : Bool Bool Bool -> Bool .
           vars X Y : S .
           vars P Q : Bool .
           eq if true then X else Y fi = X .
           eq if false then X else Y fi = Y .
           eq if true then P else Q fi = P .
           eq if false then P else Q fi = Q .
           ops f g k : Bool -> S .
           ceq f(B:Bool) = if B:Bool then a else b fi if B:Bool = B:Bool .
           ceq g(B:Bool) = a if if B:Bool then true else false fi = true .
           ceq k(B:Bool) = if B:Bool then a else b fi if if B:Bool then true else true fi = true .
         endfm
         reduce f(true) .
         reduce f(false) .
         reduce g(true) .
         reduce g(false) .
         reduce k(false) .",
        false,
    );
    assert!(
        !equations.output.contains("warning"),
        "{}",
        equations.output
    );
    assert_lines(
        &equations.output,
        &[
            "reduce in ITE : f(true) .\nrewrites: 2\nresult S: a",
            "reduce in ITE : f(false) .\nrewrites: 2\nresult S: b",
            "reduce in ITE : g(true) .\nrewrites: 2\nresult S: a",
            "reduce in ITE : g(false) .\nrewrites: 1\nresult S: g(false)",
            "reduce in ITE : k(false) .\nrewrites: 3\nresult S: b",
        ],
    );

    let rules = session.eval(
        "mod ITE-R is
           sorts Bool S .
           ops true false : -> Bool [ctor] .
           ops a b : -> S [ctor] .
           op if_then_else_fi : Bool S S -> S .
           vars X Y : S .
           eq if true then X else Y fi = X .
           eq if false then X else Y fi = Y .
           op h : Bool -> S .
           crl [r] : h(B:Bool) => if B:Bool then a else b fi if B:Bool = true .
         endm
         rewrite h(true) .
         rewrite h(false) .",
        false,
    );
    assert!(!rules.output.contains("warning"), "{}", rules.output);
    assert_lines(
        &rules.output,
        &[
            "rewrite in ITE-R : h(true) .\nrewrites: 2\nresult S: a",
            "rewrite in ITE-R : h(false) .\nrewrites: 0\nresult S: h(false)",
        ],
    );

    // An `if_then_else_fi` left side used to leave no `=` before the first `if`, which rejected the
    // whole module.
    let left = session.eval(
        "fmod ITE-LHS is
           sorts Bool S .
           ops true false : -> Bool [ctor] .
           ops a b c : -> S [ctor] .
           op if_then_else_fi : Bool S S -> S .
           ceq if B:Bool then a else b fi = c if B:Bool = true .
         endfm
         reduce if true then a else b fi .
         reduce if false then a else b fi .",
        false,
    );
    assert!(!left.output.contains("error"), "{}", left.output);
    assert_eq!(session.current(), Some("ITE-LHS"));
    assert_lines(
        &left.output,
        &["result S: c", "result S: if false then a else b fi"],
    );
}

/// H.3 lexical/source parse: a summand import with a dangling `+` is a `parse error:` naming the
/// offending terminator by its source text, at its own line, inside the enclosing module. The prior
/// definition, the current module, and the saved continuation are unchanged.
#[test]
fn dangling_summand_reports_the_terminator_and_keeps_session_state() {
    let mut session = Session::new();
    let entered = session.eval(
        "mod SUM-R is sort S . ops a b c : -> S . rl a => b . rl b => c . endm
         fmod SUM-T is sort T . op t : -> T . endfm
         mod SUMMED is pr SUM-R . endm",
        false,
    );
    assert!(entered.output.is_empty(), "{}", entered.output);
    let first = session.eval("rewrite [1] a .", false);
    assert!(first.output.contains("result S: b"), "{}", first.output);

    let rejected = session.eval("mod SUMMED is\n  pr SUM-R + SUM-T + .\nendm", false);
    assert_eq!(
        rejected.output,
        "parse error: module `SUMMED`, line 2: expected a name, found `.`"
    );
    assert_eq!(session.current(), Some("SUMMED"));

    let resumed = session.eval("continue 1 .", false);
    assert!(resumed.output.contains("result S: c"), "{}", resumed.output);
    // The installed SUMMED is still the prior definition, which does not import SUM-T.
    let absent = session.eval("reduce in SUMMED : t .", false);
    assert!(absent.output.starts_with("error:"), "{}", absent.output);
}

/// Reference H.4.1: a long unrecognized statement is skipped silently, and the next command runs in
/// the unchanged current module. The skip must not take a stack frame per token.
#[test]
fn long_unrecognized_statement_is_skipped_silently() {
    let mut session = Session::new();
    let entered = session.eval(
        "fmod SKIP-RUN is sort S . ops a b : -> S . eq a = b . endfm",
        false,
    );
    assert!(entered.output.is_empty(), "{}", entered.output);

    let input = format!("junkalpha{} .\nreduce a .", " a".repeat(20_000));
    let recovered = session.eval(&input, false);
    assert!(!recovered.exit);
    assert_eq!(
        recovered.output,
        "reduce in SKIP-RUN : a .\nrewrites: 1\nresult S: b"
    );
    assert_eq!(session.current(), Some("SKIP-RUN"));
}

/// Submit one rejected request and require exactly one diagnostic line carrying the Stable `error:`
/// severity prefix (TNK-OUT-001/003) plus the given detail.
fn assert_rejected(session: &mut Session, input: &str, detail: &str) {
    let eval = session.eval(input, false);
    assert!(!eval.exit, "{input}");
    assert!(
        eval.output.starts_with("error: ")
            && eval.output.contains(detail)
            && eval.output.lines().count() == 1,
        "{input}: expected one `error:` line containing {detail:?}, got {:?}",
        eval.output
    );
}

#[test]
fn rejected_session_requests_carry_the_error_prefix() {
    let mut session = Session::new();
    for (input, detail) in [
        ("show module .", "no current module"),
        ("show path 1 .", "no current module"),
        ("show path states 1 .", "no current module"),
        ("show search graph .", "no current module"),
        ("show frontier states .", "no current module"),
        ("show most general states .", "no current module"),
        ("reduce a .", "no current module"),
        ("continue .", "no current module"),
        ("select .", "expected a module name"),
        ("select NOSUCH .", "no module `NOSUCH`"),
        ("show bogus .", "unknown form `bogus`"),
        ("set trace .", "expected `[<option>] on|off`"),
        ("set trace maybe .", "got `maybe`"),
        ("set trace bogus on .", "unsupported option `bogus`"),
    ] {
        assert_rejected(&mut session, input, detail);
    }
    assert_eq!(session.current(), None);

    let entered = session.eval(
        "mod SHOW-DIAG is sort S . ops a b : -> S . rl [ab] : a => b [narrowing] . endm",
        false,
    );
    assert_eq!(entered.output, "");
    for (input, detail) in [
        ("show all SHOW-DIAG .", "unknown form `all`;"),
        ("show .", "expected a form"),
        ("show module NOSUCH .", "no such module `NOSUCH`"),
        ("show view NOSUCH .", "no such view"),
        ("show path 1 .", "no current search"),
        ("show path x .", "expected a state number"),
        ("show search graph .", "no current search"),
        ("show frontier states .", "no narrowing state graph"),
        ("show most general states .", "no narrowing state graph"),
        ("continue .", "no previous rewriting"),
    ] {
        assert_rejected(&mut session, input, detail);
    }

    // An ordinary search graph: a missing state and the narrowing-only displays are rejected.
    let searched = session.eval("search a =>* b .", false);
    assert!(
        searched.output.contains("Solution 1 (state 1)"),
        "{}",
        searched.output
    );
    assert!(
        session
            .eval("show path 1 .", false)
            .output
            .contains("state 1, S: b")
    );
    for (input, detail) in [
        ("show path 7 .", "no state 7"),
        (
            "show path states 1 .",
            "not available for an ordinary search",
        ),
        ("show frontier states .", "no narrowing state graph"),
        ("show most general states .", "no narrowing state graph"),
    ] {
        assert_rejected(&mut session, input, detail);
    }

    // A narrowing graph: missing states are rejected, and the search graph is no longer current.
    let narrowed = session.eval("vu-narrow [1] a =>* b .", false);
    assert!(
        narrowed.output.contains("Solution 1"),
        "{}",
        narrowed.output
    );
    assert!(
        session
            .eval("show path 1 .", false)
            .output
            .contains("state 1, S: b")
    );
    for (input, detail) in [
        ("show path 7 .", "no state 7"),
        ("show path states 7 .", "no state 7"),
        ("show search graph .", "no current search"),
    ] {
        assert_rejected(&mut session, input, detail);
    }
    assert_eq!(session.current(), Some("SHOW-DIAG"));
}

#[test]
fn rejected_inspections_and_trace_requests_keep_session_state() {
    let mut session = Session::new();
    session.eval(
        "mod KEEP-STATE is sort S . ops a b c : -> S . rl [ab] : a => b . rl [bc] : b => c . endm",
        false,
    );
    let first = session.eval("search [1] a =>* X:S .", false);
    assert!(
        first.output.contains("Solution 1 (state 0)"),
        "{}",
        first.output
    );
    for input in [
        "show all .",
        "show path 99 .",
        "show module NOSUCH .",
        "show view NOSUCH .",
        "show frontier states .",
        "show most general states .",
        "set trace bogus on .",
        "set trace maybe .",
    ] {
        let rejected = session.eval(input, false);
        assert!(
            rejected.output.starts_with("error: "),
            "{input}: {}",
            rejected.output
        );
    }
    assert_eq!(session.current(), Some("KEEP-STATE"));
    let resumed = session.eval("continue 1 .", false);
    assert!(
        resumed.output.contains("Solution 2 (state 1)"),
        "{}",
        resumed.output
    );

    // A failed select leaves the current module in place (TNK-SESSION-005).
    let rejected = session.eval("select NOSUCH .", false);
    assert!(
        rejected.output.starts_with("error: "),
        "{}",
        rejected.output
    );
    assert_eq!(session.current(), Some("KEEP-STATE"));

    // Rejected trace requests change no flag: tracing stays off, then equation tracing stays on.
    session.eval(
        "fmod TRACE-STATE is sort T . ops p q : -> T . eq p = q . endfm",
        false,
    );
    let rejected = session.eval("set trace eq on .", false);
    assert!(
        rejected.output.starts_with("error: "),
        "{}",
        rejected.output
    );
    let untraced = session.eval("reduce p .", false);
    assert!(
        !untraced.output.contains("***********"),
        "{}",
        untraced.output
    );
    assert_eq!(session.eval("set trace on .", false).output, "");
    for input in ["set trace eqs maybe .", "set trace eq off ."] {
        let rejected = session.eval(input, false);
        assert!(
            rejected.output.starts_with("error: "),
            "{input}: {}",
            rejected.output
        );
    }
    let traced = session.eval("reduce p .", false);
    assert!(
        traced.output.contains("*********** equation"),
        "{}",
        traced.output
    );
}

/// Appendix D: `load`/`sload` take the rest of the line as the path after removing one optional final
/// command dot, which is a `.` that follows whitespace or is the whole operand. A `.` glued to the path
/// stays part of the path.
#[test]
fn load_paths_drop_an_optional_final_command_dot() {
    let dir = scratch_dir("load-dot");
    std::fs::write(
        dir.join("gems.maude"),
        "fmod LOADED-GEMS is\n\
           sort Gem .\n\
           ops rough cut : -> Gem .\n\
           op polish : Gem -> Gem .\n\
           eq polish(rough) = cut .\n\
         endfm\n\
         reduce polish(rough) .\n",
    )
    .expect("write load fixture");
    let stem = dir.join("gems");
    let stem = stem.to_str().expect("UTF-8 scratch path");
    let loaded = "result Gem: cut";

    for form in [
        format!("load {stem} ."),
        format!("load {stem}\t."),
        format!("load {stem}.maude ."),
        format!("sload {stem} ."),
        format!("*** gems\nload {stem} ."),
        format!("load {stem}"),
    ] {
        let mut session = Session::new();
        assert!(session.input_complete(&format!("{form}\n")), "{form:?}");
        let out = session.eval(&form, false).output;
        assert!(out.contains(loaded), "{form:?}: {out}");
    }

    // Dotted and undotted spellings name one file, so `sload` skips it after the first load either
    // way, while `load` evaluates it again.
    let mut session = Session::new();
    let first = session.eval(&format!("sload {stem} ."), false).output;
    assert!(first.contains(loaded), "{first}");
    assert_eq!(session.eval(&format!("sload {stem}"), false).output, "");
    assert_eq!(
        session.eval(&format!("sload {stem}.maude ."), false).output,
        ""
    );
    assert_eq!(session.eval(&format!("load {stem} ."), false).output, first);

    // Only one final dot is removed, a glued dot is kept, and a lone dot leaves no path.
    assert_eq!(
        session.eval(&format!("load {stem}."), false).output,
        format!("error: cannot open file `{stem}.`")
    );
    assert_eq!(
        session.eval(&format!("load {stem} . ."), false).output,
        format!("error: cannot open file `{stem} .`")
    );
    assert_eq!(
        session.eval("load .", false).output,
        "error: load needs a file name"
    );
    std::fs::remove_dir_all(&dir).ok();
}

/// An SMT signature whose hooks are bound to fresh operator names.
const TALLY_SMT: &str = "fmod TALLY is
  sort Truth .
  op tt : -> Truth [special (id-hook SMT_Symbol (true))] .
  op ff : -> Truth [special (id-hook SMT_Symbol (false))] .
  op _/\\_ : Truth Truth -> Truth [prec 55 special (id-hook SMT_Symbol (and))] .
  op _=:=_ : Truth Truth -> Truth [prec 51 special (id-hook SMT_Symbol (===))] .
  sort Num .
  op <Nums> : -> Num [special (id-hook SMT_NumberSymbol (integers))] .
  op _plus_ : Num Num -> Num [prec 33 special (id-hook SMT_Symbol (+))] .
  op _below_ : Num Num -> Truth [prec 37 special (id-hook SMT_Symbol (<))] .
  op _=:=_ : Num Num -> Truth [prec 51 special (id-hook SMT_Symbol (===))] .
endfm";

/// An `smt-search` rejected while the command is built reports one `error:` line, with no echo, and
/// creates no search or continuation (TNK-SMT-003, Appendix K.1). Each rejection runs from a state
/// with no prior continuation.
#[test]
fn rejected_smt_searches_report_an_error_and_create_no_continuation() {
    let mut session = Session::new();
    let entered = session.eval(
        &format!(
            "{TALLY_SMT}
             mod CELLS is
               pr TALLY .
               sort Cell .
               op cell : Num -> Cell .
               op pair : Num Num -> Cell .
               var N : Num .
               var C : Cell .
               crl [step] : cell(N) => cell(N plus 1) if N below 2 = tt .
             endm"
        ),
        false,
    );
    assert_eq!(entered.output, "");
    let no_continuation = "no previous rewriting, search, or variant enumeration";
    let restrictions = "SMT rewriting restrictions";
    for (input, detail) in [
        ("smt-search cell(0) =>! C .", "=>! mode is not supported"),
        // The goal must be linear and free of SMT operators and SMT numbers.
        ("smt-search cell(0) =>* cell(N plus 1) .", restrictions),
        ("smt-search cell(0) =>* pair(N, N) .", restrictions),
        ("smt-search cell(0) =>* cell(1) .", restrictions),
        // A `such that` condition that is not an SMT equality, or that does not parse.
        (
            "smt-search cell(N) =>* C such that C := cell(0) .",
            "unsupported SMT-search condition",
        ),
        (
            "smt-search cell(N) =>* C such that nosuch(N) = tt .",
            "no parse",
        ),
    ] {
        assert_rejected(&mut session, input, detail);
        assert_rejected(&mut session, "continue .", no_continuation);
    }

    // Each module breaks one restriction on modules for rewriting modulo SMT.
    for (name, body, search) in [
        (
            "EQUATION",
            "sort Cell . ops cell twin : Num -> Cell . var N : Num .
             eq twin(N) = cell(N) .
             crl cell(N) => cell(N plus 1) if N below 2 = tt .",
            "smt-search cell(0) =>* C:Cell .",
        ),
        (
            "MEMBERSHIP",
            "sorts Cell Low . subsort Low < Cell . op cell : Num -> Cell . var N : Num .
             mb cell(0) : Low .
             crl cell(N) => cell(N plus 1) if N below 2 = tt .",
            "smt-search cell(0) =>* C:Cell .",
        ),
        (
            "NO-RULES",
            "sort Cell . op cell : Num -> Cell .",
            "smt-search cell(0) =>* C:Cell .",
        ),
        (
            "SMT-LHS",
            "sort Cell . op cell : Num -> Cell . var N : Num .
             rl cell(N plus 1) => cell(N) .",
            "smt-search cell(0) =>* C:Cell .",
        ),
        (
            "NONLINEAR-LHS",
            "sort Cell . op pair : Num Num -> Cell . var N : Num .
             rl pair(N, N) => pair(N, N plus 1) .",
            "smt-search pair(0, 0) =>* C:Cell .",
        ),
        (
            "COLLAPSE",
            "sort Cell . op cell : Num -> Cell . op none : -> Cell .
             op _&_ : Cell Cell -> Cell [assoc comm id: none] . var N : Num .
             crl cell(N) => cell(N plus 1) if N below 2 = tt .",
            "smt-search cell(0) =>* C:Cell .",
        ),
    ] {
        let entered = session.eval(
            &format!("mod CELLS-{name} is pr TALLY . {body} endm"),
            false,
        );
        assert_eq!(entered.output, "", "{name}");
        assert_rejected(&mut session, search, restrictions);
        assert_rejected(&mut session, "continue .", no_continuation);
    }

    // A valid request still echoes its query and saves a continuation.
    assert_eq!(session.eval("select CELLS .", false).output, "");
    let found = session.eval("smt-search [1] cell(0) =>* C .", false);
    assert!(
        found
            .output
            .starts_with("smt-search [1] in CELLS : cell(0) =>* C .\n")
            && !found.output.contains("error:"),
        "{}",
        found.output
    );
    let resumed = session.eval("continue 1 .", false);
    assert!(!resumed.output.contains("error:"), "{}", resumed.output);
}

/// `show modules` lists each built module once, in entry order. A dependent dropped by a failed rebuild
/// is not listed, matching `select` and `show module`, which no longer find it. Entering it again lists
/// it once, after the modules that are still built.
#[test]
fn show_modules_lists_each_built_module_once() {
    let mut session = Session::new();
    let entered = session.eval(
        "fmod SHELF is sort Book . op tome : -> Book . endfm
         fmod READER is
           including SHELF .
           op read : Book -> Book .
           eq read(tome) = tome .
         endfm
         fmod LAMP is sort Light . endfm",
        false,
    );
    assert_eq!(entered.output, "");
    let listed = |session: &mut Session| session.eval("show modules .", false).output;
    assert_eq!(listed(&mut session), "modules: SHELF READER LAMP");

    // A successful redefinition keeps the module's position.
    session.eval("fmod LAMP is sort Light . op on : -> Light . endfm", false);
    assert_eq!(listed(&mut session), "modules: SHELF READER LAMP");

    // SHELF loses `Book`, so READER's rebuild fails and READER is dropped.
    let redefined = session.eval("fmod SHELF is sort Scroll . endfm", false);
    assert!(
        redefined.output.contains("error in module `READER`"),
        "{}",
        redefined.output
    );
    assert_eq!(listed(&mut session), "modules: SHELF LAMP");
    assert!(
        session
            .eval("select READER .", false)
            .output
            .starts_with("error: ")
    );

    // Entering READER again, and then redefining it, lists it once.
    session.eval(
        "fmod READER is sort Book . op tome : -> Book . endfm",
        false,
    );
    assert_eq!(listed(&mut session), "modules: SHELF LAMP READER");
    session.eval(
        "fmod READER is sort Book . ops tome page : -> Book . endfm",
        false,
    );
    assert_eq!(listed(&mut session), "modules: SHELF LAMP READER");
    assert_eq!(session.current(), Some("READER"));
}

/// Sources for the dependent-rebuild tests below; `{BASE}` is replaced by an `ORDER-BASE` definition.
/// `ORDER-LATE` and `ORDER-VIA` are first defined before the chain they later import, so definition order
/// is not dependency order. `ORDER-VIA` reaches the chain only through the view `ORDER-V`.
const ORDER_GRAPH: &str = "fth ORDER-TRIV is sort Elt . endfth
fmod ORDER-LATE is sort Unused . endfm
fmod ORDER-VIA is sort Unused . endfm
{BASE}
fmod ORDER-L1 is pr ORDER-BASE . op k1 : -> S . eq k1 = a + b * a . endfm
fmod ORDER-L2 is pr ORDER-L1 . op k2 : -> S . eq k2 = a + b * a . endfm
fmod ORDER-L3 is pr ORDER-L2 . op k3 : -> S . eq k3 = a + b * a . endfm
fmod ORDER-L4 is pr ORDER-L3 . op k4 : -> S . eq k4 = a + b * a . endfm
view ORDER-V from ORDER-TRIV to ORDER-L4 is sort Elt to S . endv
fmod ORDER-USE{X :: ORDER-TRIV} is op id : X$Elt -> X$Elt . endfm
fmod ORDER-LATE is pr ORDER-L4 . endfm
fmod ORDER-VIA is pr ORDER-USE{ORDER-V} . endfm";

/// `ORDER-BASE`, in which `a + b * a` groups as `a + (b * a)` when `plus > times`, else `(a + b) * a`.
fn order_base(plus: u32, times: u32) -> String {
    format!(
        "fmod ORDER-BASE is sort S . ops a b : -> S .
           op _+_ : S S -> S [prec {plus}] . op _*_ : S S -> S [prec {times}] . endfm"
    )
}

/// `TNK-MOD-006` with `TNK-MOD-002` statement homes: a dependent rebuilt after an import changes equals
/// a fresh build of the same sources, including the imported statements it reparses in their home
/// modules' grammars. Every home therefore has to be rebuilt before the dependents that consult it.
#[test]
fn dependent_rebuilds_reparse_imports_with_rebuilt_home_grammars() {
    let mut rebuilt = Session::new();
    let entered = rebuilt.eval(&ORDER_GRAPH.replace("{BASE}", &order_base(33, 31)), false);
    assert_eq!(entered.output, "");
    let redefined = rebuilt.eval(&order_base(31, 33), false);
    assert_eq!(redefined.output, "");

    let mut fresh = Session::new();
    let entered = fresh.eval(&ORDER_GRAPH.replace("{BASE}", &order_base(31, 33)), false);
    assert_eq!(entered.output, "");

    let modules = [
        ("ORDER-L1", 1),
        ("ORDER-L2", 2),
        ("ORDER-L3", 3),
        ("ORDER-L4", 4),
        ("ORDER-LATE", 4),
        ("ORDER-VIA", 4),
    ];
    for (module, levels) in modules {
        for level in 1..=levels {
            let command = format!("reduce in {module} : k{level} .");
            let want = fresh.eval(&command, false).output;
            assert!(want.contains("result S: a + b * a"), "{command}: {want}");
            let got = rebuilt.eval(&command, false).output;
            assert_eq!(got, want, "{command} differs from a fresh build");
        }
    }
}

/// Strategy definitions donated by a plain import are compiled with their home module's grammar too, so a
/// rebuilt importer must see every rebuilt strategy home.
#[test]
fn dependent_rebuilds_recompile_imported_strategies_with_rebuilt_homes() {
    let base = |plus: u32, times: u32| {
        format!(
            "mod STRAT-ORDER-BASE is\n  sort S .\n  ops a b : -> S .\n  \
             op _plus_ : S S -> S [prec {plus}] .\n  op _times_ : S S -> S [prec {times}] .\nendm\n"
        )
    };
    // STRAT-ORDER-LATE is first defined before the chain it later imports. Strategy declarations and
    // definitions end their lines (`TNK-LEX-001`).
    let mut source = format!("smod STRAT-ORDER-LATE is\nendsm\n{}", base(33, 31));
    for level in 1..=4 {
        let import = match level {
            1 => "STRAT-ORDER-BASE".to_string(),
            _ => format!("STRAT-ORDER-{}", level - 1),
        };
        source.push_str(&format!(
            "smod STRAT-ORDER-{level} is\n  pr {import} .\n  strat go{level} : @ S .\n  \
             sd go{level} := match a plus b times a .\nendsm\n"
        ));
    }
    source.push_str("smod STRAT-ORDER-LATE is\n  pr STRAT-ORDER-4 .\nendsm\n");
    let mut session = Session::new();
    assert_eq!(session.eval(&source, false).output, "");
    // `a plus b times a` now groups as `(a plus b) times a`.
    assert_eq!(session.eval(&base(31, 33), false).output, "");

    let modules = [
        ("STRAT-ORDER-1", 1),
        ("STRAT-ORDER-2", 2),
        ("STRAT-ORDER-3", 3),
        ("STRAT-ORDER-4", 4),
        ("STRAT-ORDER-LATE", 4),
    ];
    for (module, levels) in modules {
        for level in 1..=levels {
            let command = format!("srewrite in {module} : (a plus b) times a using go{level} .");
            let out = session.eval(&command, false).output;
            assert!(out.contains("Solution 1"), "{command}: {out}");
        }
    }
}

/// Failed dependent rebuilds are reported in rebuild order. The exact order is this implementation's
/// choice, not a Reference promise: imports first, otherwise by first definition, so the diagnostics of
/// one redefinition are deterministic. `FAIL-LATE` was first defined before the chain it now imports.
#[test]
fn dependent_rebuild_failures_are_reported_in_dependency_order() {
    let mut session = Session::new();
    let entered = session.eval(
        "fmod FAIL-BASE is sort S . op a : -> S . endfm
         fmod FAIL-LATE is sort U . endfm
         fmod FAIL-M1 is pr FAIL-BASE . op f : S -> S . endfm
         fmod FAIL-M2 is pr FAIL-M1 . endfm
         fmod FAIL-M3 is pr FAIL-M2 . endfm
         fmod FAIL-N1 is pr FAIL-BASE . op n : S -> S . endfm
         fmod FAIL-LATE is pr FAIL-M3 . endfm",
        false,
    );
    assert_eq!(entered.output, "");
    for _ in 0..2 {
        let redefined = session.eval("fmod FAIL-BASE is sort T . endfm", false);
        let failed: Vec<&str> = redefined
            .output
            .lines()
            .filter_map(|line| line.strip_prefix("error in module `"))
            .filter_map(|rest| rest.split('`').next())
            .collect();
        assert_eq!(
            failed,
            ["FAIL-M1", "FAIL-M2", "FAIL-M3", "FAIL-LATE", "FAIL-N1"],
            "{}",
            redefined.output
        );
        for module in failed {
            let gone = session.eval(&format!("reduce in {module} : a ."), false);
            assert!(gone.output.contains("does not exist"), "{}", gone.output);
        }
        // Restore the dependents, in their original definition order, for the second pass.
        let restored = session.eval(
            "fmod FAIL-BASE is sort S . op a : -> S . endfm
             fmod FAIL-M1 is pr FAIL-BASE . op f : S -> S . endfm
             fmod FAIL-M2 is pr FAIL-M1 . endfm
             fmod FAIL-M3 is pr FAIL-M2 . endfm
             fmod FAIL-N1 is pr FAIL-BASE . op n : S -> S . endfm
             fmod FAIL-LATE is pr FAIL-M3 . endfm",
            false,
        );
        assert_eq!(restored.output, "");
    }
}

/// Modules and views have separate namespaces, so each keeps its own dependency record when they share a
/// name (`TNK-MOD-006`). A view defined with a module's name must not stop that module from being rebuilt,
/// nor may a module defined with a view's name stop the view's users from being rebuilt.
#[test]
fn module_and_view_sharing_a_name_keep_separate_dependency_records() {
    let mut session = Session::new();
    let entered = session.eval(
        "fth NS-TRIV is sort Elt . endfth
         fth NS-THV is sort Elt . op k : Elt -> Elt . endfth
         fmod NS-BASE is sort S . ops v1 v2 : -> S . op k : -> S . eq k = v1 . endfm
         fmod NS-OTHER is sort T . endfm
         fmod NS-SAME is pr NS-BASE . endfm
         view NS-SAME from NS-TRIV to NS-OTHER is sort Elt to T . endv
         fmod NS-TA is sort D . ops c r1 r2 : -> D . op p : D -> D . eq p(c) = r1 . endfm
         view NS-W from NS-THV to NS-TA is sort Elt to D . op k to p . endv
         fmod NS-USE{X :: NS-THV} is
           op probe : X$Elt -> X$Elt . var A : X$Elt . eq probe(A) = k(A) .
         endfm
         fmod NS-INST is pr NS-USE{NS-W} . endfm
         fmod NS-W is sort Other . endfm",
        false,
    );
    assert_eq!(entered.output, "");

    let redefined = session.eval(
        "fmod NS-BASE is sort S . ops v1 v2 : -> S . op k : -> S . eq k = v2 . endfm",
        false,
    );
    assert_eq!(redefined.output, "");
    let module = session.eval("reduce in NS-SAME : k .", false);
    assert!(module.output.contains("result S: v2"), "{}", module.output);

    let redefined = session.eval(
        "fmod NS-TA is sort D . ops c r1 r2 : -> D . op p : D -> D . eq p(c) = r2 . endfm",
        false,
    );
    assert_eq!(redefined.output, "");
    let view_user = session.eval("reduce in NS-INST : probe(c) .", false);
    assert!(
        view_user.output.contains("result D: r2"),
        "{}",
        view_user.output
    );
}

/// A module instantiated with a view of its own name depends on that view, and a view named like its
/// target module depends on that module. Retargeting the view, or redefining either target, rebuilds the
/// instantiating modules.
#[test]
fn same_named_view_and_target_dependencies_are_kept() {
    let mut session = Session::new();
    let entered = session.eval(
        "fth SN-THV is sort Elt . op k : Elt -> Elt . endfth
         fmod SN-TA is sort D . ops c r1 r2 r3 : -> D . op p : D -> D . eq p(c) = r1 . endfm
         fmod SN-TB is sort D . ops c r1 r2 r3 : -> D . op p : D -> D . eq p(c) = r2 . endfm
         fmod SN-USE{X :: SN-THV} is
           op probe : X$Elt -> X$Elt . var A : X$Elt . eq probe(A) = k(A) .
         endfm
         view SN from SN-THV to SN-TA is sort Elt to D . op k to p . endv
         fmod SN is pr SN-USE{SN} . endfm
         fmod SN-SAME is sort D . ops c r1 r2 : -> D . op p : D -> D . eq p(c) = r1 . endfm
         view SN-SAME from SN-THV to SN-SAME is sort Elt to D . op k to p . endv
         fmod SN-INST is pr SN-USE{SN-SAME} . endfm",
        false,
    );
    assert_eq!(entered.output, "");
    let probe = |session: &mut Session, module: &str| {
        session
            .eval(&format!("reduce in {module} : probe(c) ."), false)
            .output
    };
    assert!(probe(&mut session, "SN").contains("result D: r1"));

    let retargeted = session.eval(
        "view SN from SN-THV to SN-TB is sort Elt to D . op k to p . endv",
        false,
    );
    assert_eq!(retargeted.output, "");
    let out = probe(&mut session, "SN");
    assert!(
        out.contains("result D: r2"),
        "after retargeting the view: {out}"
    );

    let redefined = session.eval(
        "fmod SN-TB is sort D . ops c r1 r2 r3 : -> D . op p : D -> D . eq p(c) = r3 . endfm",
        false,
    );
    assert_eq!(redefined.output, "");
    let out = probe(&mut session, "SN");
    assert!(
        out.contains("result D: r3"),
        "after redefining the target: {out}"
    );

    let redefined = session.eval(
        "fmod SN-SAME is sort D . ops c r1 r2 : -> D . op p : D -> D . eq p(c) = r2 . endfm",
        false,
    );
    assert_eq!(redefined.output, "");
    let out = probe(&mut session, "SN-INST");
    assert!(out.contains("result D: r2"), "{out}");
}

/// The stock prelude names identity views after their theories (`view TRIV from TRIV to TRIV`). Such a
/// view must not replace the theory's own dependency record: redefining a module the theory imports still
/// rebuilds the theory and the modules parameterized by it.
#[test]
fn identity_view_named_after_its_theory_keeps_the_theory_dependencies() {
    let mut session = Session::new();
    let entered = session.eval(
        "fth ID-TRIV is sort Elt . endfth
         fmod ID-BASE is sort S . ops v1 v2 : -> S . op k : -> S . eq k = v1 . endfm
         fth ID-THEORY is pr ID-BASE . inc ID-TRIV . endfth
         view ID-THEORY from ID-TRIV to ID-THEORY is endv
         fmod ID-USE{X :: ID-THEORY} is op probe : -> S . eq probe = k . endfm",
        false,
    );
    assert_eq!(entered.output, "");
    let before = session.eval("reduce in ID-USE : probe .", false);
    assert!(before.output.contains("result S: v1"), "{}", before.output);

    let redefined = session.eval(
        "fmod ID-BASE is sort S . ops v1 v2 : -> S . op k : -> S . eq k = v2 . endfm",
        false,
    );
    assert_eq!(redefined.output, "");
    for command in ["reduce in ID-USE : probe .", "reduce in ID-THEORY : k ."] {
        let out = session.eval(command, false).output;
        assert!(out.contains("result S: v2"), "{command}: {out}");
    }
}

/// `TNK-STMT-001` applies to dependent rebuilds (`TNK-MOD-006`): a dependent rebuilt against a replaced
/// import reports each statement it newly drops. The home module's warning is shown once even though both
/// importers drop the statement; a drop that persists is not repeated, and one that is repaired and then
/// recurs is reported again.
#[test]
fn dependent_rebuilds_report_newly_dropped_statements_once() {
    let mut session = Session::new();
    let base = "fmod DROP-BASE is\n  sort T .\n  ops p q : -> T .\nendfm";
    let without_q = "fmod DROP-BASE is\n  sort T .\n  op p : -> T .\nendfm";
    let with_r = "fmod DROP-BASE is\n  sort T .\n  ops p r : -> T .\nendfm";
    assert_eq!(session.eval(base, false).output, "");
    let user = "fmod DROP-USE is\n  pr DROP-BASE .\n  op h : T -> T .\n  eq h(p) = q .\nendfm";
    assert_eq!(session.eval(user, false).output, "");
    let top = "fmod DROP-TOP is\n  pr DROP-USE .\nendfm";
    assert_eq!(session.eval(top, false).output, "");

    let dropped =
        "warning: module `DROP-USE`, line 4: dropped equation: no parse at token 0 (`q`): `q`";
    assert_eq!(session.eval(without_q, false).output, dropped);
    for module in ["DROP-USE", "DROP-TOP"] {
        let out = session
            .eval(&format!("reduce in {module} : h(p) ."), false)
            .output;
        assert!(
            out.contains("rewrites: 0\nresult T: h(p)"),
            "{module}: {out}"
        );
    }
    assert_eq!(session.eval(with_r, false).output, "");

    assert_eq!(session.eval(base, false).output, "");
    let repaired = session.eval("reduce in DROP-TOP : h(p) .", false).output;
    assert!(repaired.contains("rewrites: 1\nresult T: q"), "{repaired}");
    assert_eq!(session.eval(without_q, false).output, dropped);

    // A drop reported when its module was entered is not repeated when a rebuild drops it again.
    let entry = "fmod DROP-ENTRY is\n  pr DROP-BASE .\n  op k : T -> T .\n  eq k(p) = zzz .\nendfm";
    assert_eq!(
        session.eval(entry, false).output,
        "warning: module `DROP-ENTRY`, line 4: dropped equation: no parse at token 0 (`zzz`): `zzz`"
    );
    assert_eq!(session.eval(with_r, false).output, "");
}

/// A view redefinition rebuilds the modules instantiated with it (`TNK-MOD-006`); each statement kind
/// that no longer builds in a rebuilt module is dropped with a diagnostic (`TNK-STMT-001`).
#[test]
fn view_redefinition_rebuilds_report_each_dropped_statement_kind() {
    let mut session = Session::new();
    let setup = session.eval(
        "fth VDROP-PT is sort Elt . endfth
         fmod VDROP-T1 is sort A . ops a b : -> A . endfm
         fmod VDROP-T2 is sort A . op a : -> A . endfm
         view VDROP-V from VDROP-PT to VDROP-T1 is sort Elt to A . endv
         fmod VDROP-W{X :: VDROP-PT} is op w : X$Elt -> X$Elt . endfm",
        false,
    );
    assert_eq!(setup.output, "");
    let user = session.eval(
        "mod VDROP-USE is\n  pr VDROP-W{VDROP-V} .\n  sort U .\n  subsort U < A .\n  mb b : U .\n  \
         eq w(a) = b .\n  rl [r] : a => b .\nendm",
        false,
    );
    assert_eq!(user.output, "");
    let before = session.eval("rewrite in VDROP-USE : w(a) .", false).output;
    assert!(before.contains("result U: b"), "{before}");

    let retargeted = session.eval(
        "view VDROP-V from VDROP-PT to VDROP-T2 is sort Elt to A . endv",
        false,
    );
    assert_eq!(
        retargeted.output,
        "warning: module `VDROP-USE`, line 5: dropped membership: no parse at token 0 (`b`): `b`\n\
         warning: module `VDROP-USE`, line 6: dropped equation: no parse at token 0 (`b`): `b`\n\
         warning: module `VDROP-USE`, line 7: dropped rule: no parse at token 0 (`b`): `b`"
    );
    let after = session.eval("rewrite in VDROP-USE : w(a) .", false).output;
    assert!(after.contains("rewrites: 0\nresult A: w(a)"), "{after}");
}

/// An importer's build can drop a home's statement with a message of its own (it falls back to the
/// importer's grammar), attributed to the home. Such a warning is shown once and then stays suppressed
/// while that build still produces it, whichever modules are rebuilt and in whichever order.
#[test]
fn importer_attributed_drops_are_not_repeated_by_later_rebuilds() {
    let mut session = Session::new();
    let with_q = "fmod STORM-BASE is sort T . ops p q : -> T . endfm";
    let without_q = "fmod STORM-BASE is sort T . op p : -> T . endfm";
    assert_eq!(session.eval(with_q, false).output, "");
    let home = "fmod STORM-HOME is pr STORM-BASE . op h : T -> T . eq h(p) = q . endfm";
    assert_eq!(session.eval(home, false).output, "");
    let user = "fmod STORM-USE is pr STORM-HOME . sort U . op q : U -> U . endfm";
    assert_eq!(session.eval(user, false).output, "");

    // STORM-HOME no longer parses `q`; STORM-USE retries the statement in its own grammar, where `q`
    // is unary, and reports a different message for the same home statement.
    let broken = session.eval(without_q, false).output;
    let lines: Vec<&str> = broken.lines().collect();
    assert_eq!(lines.len(), 2, "{broken}");
    assert_eq!(
        lines[0],
        "warning: module `STORM-HOME`, line 1: dropped equation: no parse at token 0 (`q`): `q`"
    );
    assert!(
        lines[1].starts_with(
            "warning: module `STORM-HOME`, line 1: dropped equation: no parse at token 1"
        ),
        "{broken}"
    );
    for _ in 0..3 {
        assert_eq!(session.eval(without_q, false).output, "");
    }
}

/// A shown drop is forgotten once no built module still produces it, so a recurrence is reported again:
/// both when only the importer that produced it is rebuilt and when that importer is entered again.
#[test]
fn recurring_importer_attributed_drops_are_reported_again() {
    let mut session = Session::new();
    let home = session.eval(
        "fmod RECUR-X is sort T . op p : -> T . op h : T -> T . eq h(p) = q . endfm",
        false,
    );
    assert!(
        home.output.starts_with("warning: module `RECUR-X`"),
        "{}",
        home.output
    );
    let unary_q = "fmod RECUR-B is sort U . op q : U -> U . endfm";
    assert_eq!(session.eval(unary_q, false).output, "");
    let user = session.eval("fmod RECUR-Y is pr RECUR-X . pr RECUR-B . endfm", false);
    let variant = user.output;
    assert!(
        variant.starts_with("warning: module `RECUR-X`"),
        "{variant}"
    );

    // Only RECUR-Y is rebuilt (RECUR-X does not import RECUR-B); now its grammar parses the equation.
    let constant_q = "fmod RECUR-B is pr RECUR-X . op q : -> T . endfm";
    assert_eq!(session.eval(constant_q, false).output, "");
    let repaired = session.eval("reduce in RECUR-Y : h(p) .", false).output;
    assert!(repaired.contains("rewrites: 1\nresult T: q"), "{repaired}");
    assert_eq!(session.eval(unary_q, false).output, variant);
    let broken = session.eval("reduce in RECUR-Y : h(p) .", false).output;
    assert!(broken.contains("rewrites: 0\nresult T: h(p)"), "{broken}");

    // The same recurrence through direct re-entry of an importer, with a home of its own: RECUR-Y still
    // produces (and so still suppresses) the RECUR-X variant.
    let second = session.eval(
        "fmod RECUR-X2 is sort T2 . op p2 : -> T2 . op h2 : T2 -> T2 . eq h2(p2) = r . endfm",
        false,
    );
    assert!(
        second.output.starts_with("warning: module `RECUR-X2`"),
        "{}",
        second.output
    );
    let original = "fmod RECUR-Z is pr RECUR-X2 . sort V . op r : V -> V . endfm";
    let first = session.eval(original, false).output;
    assert!(first.starts_with("warning: module `RECUR-X2`"), "{first}");
    let replacement = "fmod RECUR-Z is pr RECUR-X2 . op r : -> T2 . endfm";
    assert_eq!(session.eval(replacement, false).output, "");
    assert_eq!(session.eval(original, false).output, first);
}
