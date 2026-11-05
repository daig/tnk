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
