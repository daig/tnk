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
