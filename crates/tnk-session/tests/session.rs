use tnk_session::Session;

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
            shown.output.contains("no such module"),
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
