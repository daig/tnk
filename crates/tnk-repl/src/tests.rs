//! `eval`-driven tests for the terminal-neutral REPL. Each test submits input and exercises the complete
//! parse → flatten → build → execute → render pipeline.

use super::*;

fn repl() -> Repl {
    Repl::new(false) // uncolored, for deterministic output
}

macro_rules! conformance_file {
    ($n:expr) => {
        include_str!(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../conformance/",
            $n
        ))
    };
}

/// Entering a module makes it current; a command in a *separate* submission (no module of its own — the
/// REPL case that `parse_source` rejects) binds to it.
#[test]
fn enter_module_then_reduce_across_submissions() {
    let mut r = repl();
    let ev = r.eval(
        "fmod COLOR is sort C . ops red green : -> C [ctor] . op f : C -> C . eq f(red) = green . endfm",
    );
    assert!(!ev.exit);
    assert_eq!(r.current(), Some("COLOR"));

    let out = r.eval("red f(red) .").output;
    assert!(out.contains("reduce in COLOR :"), "header: {out}");
    assert!(out.contains("rewrites: 1"), "count: {out}");
    assert!(out.contains("result C: green"), "result: {out}");
}

/// A command with no current module is a friendly error, not a panic.
#[test]
fn command_without_current_module() {
    let mut r = repl();
    assert!(r.eval("red foo .").output.contains("no current module"));
}

/// The stock REPL deliberately has no host-function catalog. A host attachment is rejected while the
/// module is built rather than becoming an inert ordinary operator.
#[test]
fn stock_repl_rejects_strict_host_function_without_catalog() {
    let mut r = repl();
    assert_eq!(
        r.eval("fmod BASE is sort S . op a : -> S [ctor] . endfm")
            .output,
        ""
    );

    let failed = r.eval(
        r#"fmod HOST-REPL is
  sort S .
  op a : -> S [ctor] .
  op host : S -> S
    [special (id-hook HostFunctionSymbol (testing.echo))] .
endfm"#,
    );
    assert!(
        failed.output.contains("missing host")
            && failed.output.contains("capability `testing.echo`"),
        "{}",
        failed.output
    );
    assert_eq!(r.current(), Some("BASE"));
    let missing = r.eval("reduce in HOST-REPL : host(a) .");
    assert!(
        missing.output.contains("module `HOST-REPL` does not exist"),
        "{}",
        missing.output
    );
}

/// A diamond import produces the expected value and accumulated rewrite count.
#[test]
fn import_diamond_through_repl() {
    let out = repl()
        .eval(conformance_file!("import-diamond.maude"))
        .output;
    assert!(out.contains("rewrites: 12"), "count: {out}");
    assert!(out.contains("result N: s(s(s(s(s(0)))))"), "value: {out}");
}

/// Renaming through the REPL: `top(e) = box(e) = e`, sort renamed to `Item`.
#[test]
fn import_renaming_through_repl() {
    let out = repl()
        .eval(conformance_file!("import-renaming.maude"))
        .output;
    assert!(out.contains("result Item: e"), "value: {out}");
    assert!(out.contains("rewrites: 2"), "count: {out}");
}

/// Loads `LIST{Nat}` and exercises AU identity collapse, matching, and parameter instantiation.
#[test]
fn prelude_list_through_repl() {
    let out = repl().eval(conformance_file!("prelude-list.maude")).output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "LIST builds: {out}"
    );
    let lines: Vec<&str> = out
        .lines()
        .filter(|l| l.starts_with("result ") || l.starts_with("rewrites:"))
        .collect();
    // Pair each `rewrites:`/`result` into `[count] sort: value`, then compare the whole sequence.
    let got: Vec<String> = lines
        .chunks(2)
        .map(|c| {
            let n = c[0]
                .trim_start_matches("rewrites: ")
                .split(' ')
                .next()
                .unwrap_or("?");
            format!("[{n}] {}", c[1].trim_start_matches("result "))
        })
        .collect();
    assert_eq!(
        got,
        vec![
            "[6] Bool: true",           // occurs(2, 1 2 3)
            "[9] Bool: true",           // occurs(3, 1 2 3)  — recurses to the singleton
            "[10] Bool: false",         // occurs(5, 1 2 3)  — recurses past the singleton to nil
            "[3] Bool: true",           // occurs(7, 7)      — singleton subject
            "[12] NzNat: 5",            // size(1 2 3 4 5)
            "[4] NzNat: 1",             // size(7)           — collapse
            "[2] Zero: 0",              // size(nil)
            "[6] NeList{Nat}: 4 3 2 1", // reverse(1 2 3 4)
            "[3] NzNat: 7",             // reverse(7)
            "[2] List{Nat}: nil",       // reverse(nil)
            "[1] NzNat: 3",             // last(1 2 3)
            "[1] NeList{Nat}: 1 2",     // front(1 2 3)
            "[1] NeList{Nat}: 1 2 3 4", // append(1 2, 3 4)
        ],
        "LIST ops: {out}"
    );
}

/// Loads EXT-BOOL and `SET{Nat}` and exercises kind syntax, ACU identity collapse, nonlinear matching, and
/// associative-list rendering.
#[test]
fn prelude_set_through_repl() {
    let out = repl().eval(conformance_file!("prelude-set.maude")).output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "SET builds: {out}"
    );
    let lines: Vec<&str> = out
        .lines()
        .filter(|l| l.starts_with("result ") || l.starts_with("rewrites:"))
        .collect();
    let got: Vec<String> = lines
        .chunks(2)
        .map(|c| {
            let n = c[0]
                .trim_start_matches("rewrites: ")
                .split(' ')
                .next()
                .unwrap_or("?");
            format!("[{n}] {}", c[1].trim_start_matches("result "))
        })
        .collect();
    assert_eq!(
        got,
        vec![
            "[1] Bool: false",            // true and-then false
            "[1] Bool: true",             // false or-else true
            "[1] Bool: true",             // 2 in (1, 2, 3)
            "[1] Bool: false", // 5 in (1, 2, 3)   — absent, recurses to singleton (non-linear)
            "[1] Bool: true",  // 7 in 7           — singleton subject (collapse)
            "[8] NzNat: 3",    // | (1, 2, 3) |
            "[4] NzNat: 1",    // | 7 |
            "[6] Bool: false", // (1, 5) subset (1, 2, 3)
            "[7] Bool: true",  // (1, 2) subset (1, 2, 3)
            "[2] NeSet{Nat}: 1, 3", // delete(2, (1, 2, 3))
            "[1] NeSet{Nat}: 1, 2, 3, 4", // insert(4, (1, 2, 3))
            "[1] NeSet{Nat}: 1, 2, 3, 4", // union((1, 2), (3, 4))
            "[11] NeSet{Nat}: 2, 3", // intersection((1, 2, 3), (2, 3, 4))
            "[11] NeSet{Nat}: 1, 3", // (1, 2, 3) \ (2, 4)
        ],
        "SET ops: {out}"
    );
}

/// Collect ordered strategy solution values per command, preserving multiline values.
fn strategy_solutions(out: &str) -> Vec<String> {
    let mut res = Vec::new();
    let mut cur: Vec<String> = Vec::new();
    let (mut active, mut none) = (false, false);
    for line in out.lines() {
        if line.starts_with("srewrite ") || line.starts_with("dsrewrite ") {
            if active {
                res.push(if none {
                    "(no solution)".to_string()
                } else {
                    cur.join(" ; ")
                });
            }
            cur = Vec::new();
            active = true;
            none = false;
        } else if let Some(v) = line.strip_prefix("result ") {
            if let Some(idx) = v.find(": ") {
                cur.push(v[idx + 2..].to_string());
            }
        } else if line.starts_with("No solution.") {
            none = true;
        }
    }
    if active {
        res.push(if none {
            "(no solution)".to_string()
        } else {
            cur.join(" ; ")
        });
    }
    res
}

/// Exercise primitive actions, combinators, tests, named and recursive calls, parameters, and matchrew in
/// fair and depth-first execution.
#[test]
fn strategy_core_through_repl() {
    let out = repl().eval(conformance_file!("strategy.maude")).output;
    assert!(
        !out.contains("no parse") && !out.contains("error:"),
        "strategy core builds/runs: {out}"
    );
    assert_eq!(
        strategy_solutions(&out),
        vec![
            "b",             // r1
            "b ; c",         // r1 | r2
            "d",             // r1 ; r3
            "a ; b",         // r1 * (zero-or-more)
            "b ; c",         // all
            "a",             // idle
            "(no solution)", // fail
            "b",             // top(r1)
            "(no solution)", // match b — a doesn't match b
            "a",             // match a — succeeds, returns the subject
            "(no solution)", // amatch d — d occurs nowhere in a
            "d",             // r1 ? r3 : r2 — r1 succeeds → r3 on b
            "(no solution)", // r2 ? r3 : r4 — r2 succeeds → r3 on c fails (no γ)
            "b ; c",         // (r1 | r2) ! — normalization to the strategy's normal forms
            "b",             // r1 +
            "b",             // try(r1)
            "a",             // not(fail)
            "d",             // (r1 ; r3) | (r2 ; r4)
            "b",             // one(r1 | r2) — only the first solution
            "b ; c",         // dsrewrite r1 | r2
            "d",             // dsrewrite (r1 | r2) ; r3
            // Named definitions and calls, including a recursive reachability strategy. Depth-first
            // execution terminates through cycle pruning.
            "d",             // srewrite go
            "d ; c",         // dsrewrite go2
            "a ; b ; d ; c", // dsrewrite reach — all states reachable from a (recursion terminates)
            // Matchrew forms, conditional rules, application substitutions, tests, and parameterized calls.
            "f(b, c)",                               // matchrew by X using r1, Y using r2
            "f(b, b) ; f(c, b)",                     // matchrew by X using (r1|r2), Y using r1
            "f(b, b) ; f(c, b) ; f(b, c) ; f(c, c)", // dsrewrite matchrew — full cartesian product
            "f(b, a)",           // matchrew by X using r1 — partial by-list (Y kept)
            "(no solution)",     // matchrew f(b,a) … X using r1 — r1 fails on b
            "f(b, a) ; f(a, b)", // amatchrew X by X using r1 — anywhere
            "g(b)",              // wrap{r1} — rewrite condition solved by r1
            "g(c)",              // wrap{r2}
            "g(b) ; g(c)",       // dsrewrite wrap{r1 | r2}
            "(no solution)",     // wrap — bare rewrite-conditional rule cannot apply
            "d",                 // eqc — equality condition holds
            "(no solution)",     // eqf — equality condition fails
            "f(b, a)",           // swap — plain
            "f(b, a)",           // swap[X <- a] — consistent constraint
            "(no solution)",     // swap[X <- b] — inconsistent with the match
            "a . a . a",         // xmatch X . Y — extension test returns the subject
            "a . a . a",         // match X . Y — whole-match test returns the subject
            "b",                 // s2(a) — parameterized call
            "b",                 // go3 := s2(a)
            "b",                 // mtest(b) := match b — parameter used in a pattern
            "(no solution)",     // mtest(a) := match a — fails on subject b
        ],
        "strategy solutions: {out}"
    );
}

/// Per `srewrite`/`dsrewrite` command, each solution as `value[cumulative-rewrite-count]` joined by ` ; `
/// (or `(no solution)`). The `rewrites:` line precedes each `result`, so each result pairs with the most
/// recent count. Pins the fair-`srewrite` solution ORDER **and** per-solution count (unlike
/// [`strategy_solutions`], which pins only values).
fn strategy_value_counts(out: &str) -> Vec<String> {
    let mut res = Vec::new();
    let mut cur: Vec<String> = Vec::new();
    let (mut active, mut rw) = (false, String::new());
    for line in out.lines() {
        if line.starts_with("srewrite ") || line.starts_with("dsrewrite ") {
            if active {
                res.push(cur.join(" ; "));
            }
            cur = Vec::new();
            active = true;
        } else if let Some(n) = line.strip_prefix("rewrites: ") {
            rw = n.split(' ').next().unwrap_or("?").to_string();
        } else if let Some(v) = line.strip_prefix("result ") {
            if let Some((_, val)) = v.split_once(": ") {
                cur.push(format!("{val}[{rw}]"));
            }
        } else if line.starts_with("No solution.") {
            cur.push("(no solution)".to_string());
        }
    }
    if active {
        res.push(cur.join(" ; "));
    }
    res
}

/// Pin fair FIFO and depth-first strategy order together with cumulative rewrite counts.
#[test]
fn strategy_fair_counts_through_repl() {
    let out = repl().eval(conformance_file!("strategy-fair.maude")).output;
    assert!(
        !out.contains("no parse") && !out.contains("error:"),
        "fair strategy builds/runs: {out}"
    );
    assert_eq!(
        strategy_value_counts(&out),
        vec![
            "c[2] ; g[4]", // srew (r1;p;pp) | r2 — fair emits the shorter derivation (c) first
            "g[3] ; c[4]", // dsrew — left branch explored fully first
            "c[1] ; d[5] ; g[6]", // srew r2 | (r1;p) | (r1;p;pp) — n-ary union decompose timing
            "c[1] ; d[3] ; g[6]", // dsrew
            "d[4] ; e[4]", // srew (r1;p) | (r2;q) — equal depth, both at the level's final count
            "a[0] ; b[2] ; c[2]", // srew (r1|r2)* — reachable set, fair count snapshot
            "a[0] ; b[1] ; c[2]", // dsrew (r1|r2)* — depth-first count snapshot
            "c[2] ; b[2]", // srew r2 | r1 — the 2nd branch rewrites before the 1st emits
            "e[5] ; g[5]", // srew (r1|r2) ; (p ? pp : q) — interleaved branch sub-tasks
            "b[1] ; c[2]", // dsrew (r1|r2)! — normalize, depth-first
        ],
        "fair srewrite order+count: {out}"
    );
}

/// Every strategy command echo must parse back to the same tree. The fixture covers precedence and
/// right-nested sequence/union groupings, then compares solution order and rewrite counts after replay.
#[test]
fn strategy_echoes_round_trip_through_repl() {
    let mut r = repl();
    let setup = r.eval(
        r#"
smod STRAT-ECHO-ROUNDTRIP is
  sort S .
  ops a b c d : -> S [ctor] .
  op f : S S -> S [ctor] .
  op g : S -> S [ctor] .
  rl [r1] : a => b .
  rl [r2] : a => c .
  rl [r3] : b => d .
  rl [r4] : c => d .
  crl [wrap] : a => g(Z:S) if a => Z:S .
endsm
"#,
    );
    assert!(
        !setup.output.contains("error") && !setup.output.contains("no parse"),
        "strategy round-trip module: {}",
        setup.output
    );

    let cases = [
        ("a", "(r1 | r2) !", "(r1 | r2)!"),
        ("a", "(r1 | r2) ; (r3 | r4)", "(r1 | r2) ; (r3 | r4)"),
        ("a", "(r1 | r2) ? r3 : r4", "r1 | r2 ? r3 : r4"),
        ("a", "r3 ? r4 : (r1 | r2)", "r3 ? r4 : r1 | r2"),
        ("a", "(r1 ? r3 : r4) | r2", "(r1 ? r3 : r4) | r2"),
        (
            "a",
            "try((r1 | r2) ; (r3 | r4))",
            "try((r1 | r2) ; (r3 | r4))",
        ),
        ("a", "not((r1 | r2) ; fail)", "not((r1 | r2) ; fail)"),
        ("a", "top(r1) | r2", "top(r1) | r2"),
        ("a", "r1 | (r2 | fail)", "r1 | (r2 | fail)"),
        ("a", "r1 ; (r3 ; idle)", "r1 ; (r3 ; idle)"),
        ("a", "(r1 +) *", "r1 + *"),
        ("a", "wrap{r1 | r2}", "wrap{r1 | r2}"),
        (
            "f(a, a)",
            "matchrew f(X:S, Y:S) by X:S using (r1 | r2), Y:S using r1",
            "matchrew f(X:S, Y:S) by X:S using (r1 | r2), Y:S using r1",
        ),
    ];

    for (subject, original, expected_echo) in cases {
        let first = r
            .eval(&format!("srewrite {subject} using {original} ."))
            .output;
        assert!(
            !first.contains("error") && !first.contains("no parse"),
            "original `{original}`: {first}"
        );
        let header = first
            .split_once("\n\n")
            .map_or(first.as_str(), |(header, _)| header);
        let echoed = header
            .split_once(" using ")
            .and_then(|(_, strategy)| strategy.strip_suffix(" ."))
            .unwrap_or_else(|| panic!("malformed echo for `{original}`: {header}"));
        // Mixfix `format` attributes may make the subject/strategy command header multiline; newlines are
        // source whitespace, so compare and replay its token-equivalent one-line spelling.
        let emitted = echoed.split_whitespace().collect::<Vec<_>>().join(" ");
        assert_eq!(emitted, expected_echo, "echo for `{original}`");

        let replay = r
            .eval(&format!("srewrite {subject} using {emitted} ."))
            .output;
        assert!(
            !replay.contains("error") && !replay.contains("no parse"),
            "replayed `{emitted}`: {replay}"
        );
        assert_eq!(
            strategy_value_counts(&first),
            strategy_value_counts(&replay),
            "behavior changed after echo/reparse: `{original}` -> `{emitted}`"
        );
    }
}

fn prelude_results(out: &str) -> Vec<String> {
    let lines: Vec<&str> = out.lines().collect();
    let mut results = Vec::new();
    let mut rw = "?";
    let mut i = 0;
    while i < lines.len() {
        if let Some(rest) = lines[i].strip_prefix("rewrites: ") {
            rw = rest.split(' ').next().unwrap_or("?");
        } else if let Some(value) = lines[i].strip_prefix("result ") {
            let mut block = vec![value.to_string()];
            let mut j = i + 1;
            while j < lines.len()
                && !lines[j].starts_with("reduce ")
                && !lines[j].starts_with("rewrites:")
            {
                block.push(lines[j].to_string());
                j += 1;
            }
            results.push(format!("[{rw}] {}", block.join("\n")));
            i = j;
            continue;
        }
        i += 1;
    }
    results
}

/// End-to-end META-LEVEL coverage for reduction, rewriting, matching, application, search/path, reflection,
/// sort/kind queries, well-formedness, parsing, and printing. Also covers grammar-sensitive mixfix renaming,
/// module constructors inside equations, and kind-directed overload selection.
#[test]
fn prelude_meta_through_repl() {
    let out = repl().eval(conformance_file!("prelude-meta.maude")).output;
    assert!(
        !out.lines()
            .any(|line| line.starts_with("error") || line.starts_with("parse error")),
        "META tower builds: {out}"
    );
    assert_eq!(
        prelude_results(&out),
        vec![
            // META tower loading and grammar-sensitive module projections.
            "[1] NeSortSet: 'a ; 'b",
            "[1] Sort: 'FOO",
            "[1] RuleSet: (none).RuleSet",
            // Reduction through a named meta-module plus Qid-classified projections.
            "[2] ResultPair: {'0.Zero, 'Zero}",
            "[3] ResultPair: {'s_^5['0.Zero], 'NzNat}",
            "[3] ResultPair: {'false.Bool, 'Bool}",
            "[6] Sort: 'foo",
            "[7] Sort: 'Bar",
            // Inline meta-modules with imports, subsorts, attributed operators, and equations.
            "[3] ResultPair: {'s_^6['0.Zero], 'NzNat}",
            "[8] ResultPair: {'s_^3['0.Zero], 'NzNat}",
            // Rewriting, matching, application, and search with formatted substitutions and rules.
            "[3] ResultPair: {'c.Elt, 'Elt}", // metaRewrite unbounded: a=>b=>c
            "[2] ResultPair: {'b.Elt, 'Elt}", // metaRewrite [1]: one step a=>b
            "[3] ResultPair: {'c.Elt, 'Elt}", // metaFrewrite gas 1: a=>b=>c
            "[2] Assignment: \n  'N:Nat <- 's_^4['0.Zero]", // metaMatch: s_(N) <-> s^5(0)
            "[2] Substitution?: (noMatch).Substitution?", // metaMatch: _+_ vs s^5 — no match
            "[2] ResultTriple: {'b.Elt, 'Elt, \n  'X:Elt <- 'b.Elt}", // metaSearch =>+ sol 0: a=>b
            "[3] ResultTriple: {'c.Elt, 'Elt, \n  'X:Elt <- 'c.Elt}", // metaSearch =>+ sol 1: a=>c (ab)
            "[4] ResultTriple: {'c.Elt, 'Elt, (none).Substitution}", // normal form snapshot at confirmation
            // metaApply: the labelled rule `unwrap` (f(N) => N) at the top, its binding, or failure.
            "[2] ResultTriple: {'s_^3['0.Zero], 'NzNat, \n  'N:Nat <- 's_^3['0.Zero]}", // apply at top
            "[1] ResultTriple?: (failure).ResultTriple?", // solution 1 — past the last
            "[1] ResultTriple?: (failure).ResultTriple?", // no top match (subject is s^3(0))
            // metaXmatch (extension match → {subst, context}) and metaXapply (rule at a position →
            // {term, type, subst, context}). The hole `[]` marks the matched/rewritten position: `[]` at
            // the top, `'f[[]]` at the inner f; the substitution's `_<-_` newline-indents (`format`).
            "[2] MatchPair: {\n  'N:Nat <- 's_^4['0.Zero], []}", // metaXmatch s_(N) <-> s^5(0)
            "[2] MatchPair?: (noMatch).MatchPair?",              // metaXmatch _+_ vs s^5 — no match
            "[2] Result4Tuple: {'f['0.Zero], 'Nat, \n  'N:Nat <- 'f['0.Zero], []}", // xapply at top
            "[2] Result4Tuple: {'f['0.Zero], 'Nat, \n  'N:Nat <- '0.Zero, 'f[[]]}", // xapply at inner f
            // metaSearchPath returns the witness TraceStep with its fully formatted source rule.
            "[3] TraceStep: {'a.Elt, 'Elt, rl 'a.Elt => 'c.Elt [label('ab)] .}",
            // A two-step path is an associative Trace whose format places each step on a new line.
            "[3] Trace: {'a.Elt, 'Elt, rl 'a.Elt => 'b.Elt [label('r1)] .}\n\
             {'b.Elt, 'Elt, rl 'b.Elt => 'c.Elt [label('r2)] .}",
            // Sort/kind queries over the down-translated module lattice.
            "[2] Bool: true",                      // sortLeq(Zero, Nat)
            "[2] Bool: false",                     // sameKind(Nat, Bool)
            "[2] Sort: 'NzNat",                    // leastSort(2 + 3)
            "[2] NeSortSet: 'NzNat ; 'Zero",       // lesserSorts(Nat)
            "[2] Sort: 'NzNat",                    // glbSorts(Nat, NzNat)
            "[2] Sort: 'Nat",                      // completeName(Nat)
            "[2] Kind: '`[Nat`]",                  // getKind(Nat)
            "[2] NeKindSet: '`[Bool`] ; '`[Nat`]", // getKinds
            "[2] Sort: 'Nat",                      // maximalSorts([Nat])
            "[2] NeSortSet: 'NzNat ; 'Zero",       // minimalSorts([Nat])
            "[2] NeTypeList: 'Nat 'Nat",           // maximalAritySet(_+_)
            // wellFormed: module/term/substitution. The ill-typed term/binding return false.
            "[2] Bool: true",  // wellFormed(2 + 3)
            "[2] Bool: false", // wellFormed(true + 0) — ill-typed
            "[2] Bool: true",  // wellFormed(X:Nat <- 0)
            "[2] Bool: false", // wellFormed(X:Nat <- true) — kind clash
            // upModule + the up* projections. Non-flat lists imports + own decls; flat (S4-LIST, no
            // imports) inlines everything with a `nil` import list. Empty sets render `none`. Exercises
            // the iter-chain collapse (`s s 0` → `'s_^2['0.Zero]`), the `id:` attribute, conditional eqs,
            // and a system module's labelled (`crl`) rules.
            "[1] FModule: fmod 'S4-FOO is\n  protecting 'NAT .\n  sorts 'Bar ; 'Foo .\n  \
             subsort 'Foo < 'Bar .\n  op 'c : nil -> 'Foo [ctor] .\n  \
             op 'f : 'Foo 'Nat -> 'Bar [ctor] .\n  op 'g : 'Bar -> 'Bar [none] .\n  none\n  \
             eq 'g['X:Bar] = 'X:Bar [none] .\nendfm",
            "[1] FModule: fmod 'S4-LIST is\n  nil\n  sorts 'Elt ; 'Lst .\n  subsort 'Elt < 'Lst .\n  \
             op '__ : 'Lst 'Lst -> 'Lst [assoc id('nil.Lst)] .\n  op 'a : nil -> 'Elt [ctor] .\n  \
             op 'b : nil -> 'Elt [ctor] .\n  op 'nil : nil -> 'Lst [ctor] .\n  none\n  \
             ceq 'a.Elt = 'b.Elt if 'a.Elt = 'b.Elt [none] .\nendfm",
            "[1] FModule: fmod 'S4-NUM is\n  protecting 'NAT .\n  sorts none .\n  none\n  \
             op 'two : nil -> 'Nat [none] .\n  none\n  eq 'two.Nat = 's_^2['0.Zero] [none] .\nendfm",
            "[1] SModule: mod 'S4-SYS is\n  nil\n  sorts 'St .\n  none\n  op 'a : nil -> 'St [ctor] .\n  \
             op 'b : nil -> 'St [ctor] .\n  op 'c : nil -> 'St [ctor] .\n  none\n  none\n  \
             rl 'a.St => 'b.St [label('r1)] .\n  crl 'b.St => 'c.St if 'b.St = 'b.St [label('r2)] .\nendm",
            "[1] Import: protecting 'NAT .", // upImports
            "[1] NeSortSet: 'Bar ; 'Foo",    // upSorts (own)
            "[1] OpDeclSet: op 'c : nil -> 'Foo [ctor] .\n\
             op 'f : 'Foo 'Nat -> 'Bar [ctor] .\nop 'g : 'Bar -> 'Bar [none] .", // upOpDecls
            "[1] Equation: ceq 'a.Elt = 'b.Elt if 'a.Elt = 'b.Elt [none] .", // upEqs (conditional)
            "[1] RuleSet: rl 'a.St => 'b.St [label('r1)] .\n\
             crl 'b.St => 'c.St if 'b.St = 'b.St [label('r2)] .", // upRls
            // upTerm reduces its argument then ups it; downTerm builds (the ambient reduces), returning
            // the default `99` when the meta-term is unresolvable.
            "[2] GroundTerm: 's_^3['0.Zero]", // upTerm(1 + 2)
            "[1] NzNat: 4",                   // downTerm(s^4(0), 0)
            "[1] NzNat: 99",                  // downTerm(bogus, 99) → default
            // metaParse parses (no reduce) → {term, sort}; noParse(n) on failure. metaPrettyPrint renders
            // a term to a QidList via the format-aware printer.
            "[2] ResultPair: {'_+_['s_['0.Zero], 's_^2['0.Zero]], 'NzNat}", // metaParse(1 + 2)
            "[2] ResultPair?: noParse(0)",                                  // metaParse(foo bar)
            "[3] NeTypeList: '2 '+ '3", // metaPrettyPrint(2 + 3)
            // upView decomposes a view: header, from/to module exprs, and its sort/op maps.
            "[1] View: view 'S4-V from 'TRIV to 'NAT is\n  sort 'Elt to 'Nat .\n  none\n  none\nendv",
            // Strategy reflection over a strategy-free module returns the two typed empty sets.
            "[1] StratDeclSet: (none).StratDeclSet",
            "[1] StratDefSet: (none).StratDefSet",
        ],
        "META tower reduces: {out}"
    );
}

/// Exercise LEXICAL tokenization, punctuation/backquote canonicalization, and byte-level token printing.
#[test]
fn lexical_token_hooks_through_repl() {
    let mut r = repl();
    r.eval(conformance_file!("prelude-meta.maude"));
    let out = r
        .eval(
            r#"fmod LEXICAL is
  protecting QID-LIST .
  op printTokens : QidList -> String
    [special (id-hook QuotedIdentifierOpSymbol (printTokens)
              op-hook stringSymbol (<Strings> : ~> String)
              op-hook quotedIdentifierSymbol (<Qids> : ~> Qid)
              op-hook nilQidListSymbol (nil : ~> QidList)
              op-hook qidListSymbol (__ : QidList QidList ~> QidList))] .
  op tokenize : String -> QidList
    [special (id-hook QuotedIdentifierOpSymbol (tokenize)
              op-hook stringSymbol (<Strings> : ~> String)
              op-hook quotedIdentifierSymbol (<Qids> : ~> Qid)
              op-hook nilQidListSymbol (nil : ~> QidList)
              op-hook qidListSymbol (__ : QidList QidList ~> QidList))] .
endfm
red in LEXICAL : tokenize("") .
red in LEXICAL : tokenize("alpha") .
red in LEXICAL : tokenize("alpha beta gamma") .
red in LEXICAL : tokenize("f(a,b) _+_ `[ x`y") .
red in LEXICAL : tokenize("--- not a comment *** neither") .
red in LEXICAL : tokenize("ab\
cd") .
red in LEXICAL : tokenize("café λ") .
red in LEXICAL : printTokens(nil) .
red in LEXICAL : printTokens('alpha) .
red in LEXICAL : printTokens('f '`( 'a '`, 'b '`) '`[ '`] '`{ '`} '_+_) .
red in LEXICAL : printTokens('\n '\t '\s '\\) .
fmod LEXICAL-PARSE is
  sorts List Elt .
  subsort Elt < List .
  op __ : List List -> List [assoc] .
endfm
red in META-LEVEL : metaParse(['LEXICAL-PARSE], none, 'A:List 'B:List, anyType) .
red in META-LEVEL : metaParse(['LEXICAL-PARSE], 'A:List ; 'B:List, 'A 'B, anyType) .
"#,
        )
        .output;
    assert_eq!(
        prelude_results(&out),
        vec![
            "[1] QidList: nil",
            "[1] Qid: 'alpha",
            "[1] NeQidList: 'alpha 'beta 'gamma",
            "[1] NeQidList: 'f '`( 'a '`, 'b '`) '_+_ '`[ 'x`y",
            "[1] NeQidList: '--- 'not 'a 'comment '*** 'neither",
            "[1] Qid: 'abcd",
            "[1] NeQidList: 'café 'λ",
            "[1] String: \"\"",
            "[1] String: \"alpha\"",
            "[1] String: \"f (a ,b )[]{ }_+_\"",
            "[1] String: \"\\n\\t \\\\\"",
            "[2] ResultPair: {'__['A:List, 'B:List], 'List}",
            "[2] ResultPair: {'__['A:List, 'B:List], 'List}",
        ],
        "LEXICAL hooks: {out}"
    );
}

/// Qid-family free order-sorted unification follows sort order and ends with a typed exhaustion sentinel.
#[test]
fn free_meta_unify_indices_through_repl() {
    let mut r = repl();
    r.eval(conformance_file!("prelude-meta.maude"));
    let out = r
        .eval(
            r#"fmod FREE-MULTI is
  sorts A B C D Top .
  subsorts C D < A B < Top .
endfm
red in META-LEVEL : metaUnify(['FREE-MULTI], 'X:A =? 'Y:B, '%, 0) .
red in META-LEVEL : metaUnify(['FREE-MULTI], 'X:A =? 'Y:B, '%, 1) .
red in META-LEVEL : metaUnify(['FREE-MULTI], 'X:A =? 'Y:B, '%, 2) .
"#,
        )
        .output;
    assert_eq!(
        prelude_results(&out),
        vec![
            "[2] UnificationPair: {\n  'X:A <- '#1:C ; \n  'Y:B <- '#1:C, '#}",
            "[2] UnificationPair: {\n  'X:A <- '#1:D ; \n  'Y:B <- '#1:D, '#}",
            "[2] UnificationPair?: (noUnifier).UnificationPair?",
        ],
        "free metaUnify indices: {out}"
    );
}

/// Load `MAP{Nat, Nat}` and exercise two-parameter instantiation, kind ranges, identity attributes, lookup,
/// and membership queries.
#[test]
fn prelude_map_through_repl() {
    let out = repl().eval(conformance_file!("prelude-map.maude")).output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "MAP builds: {out}"
    );
    assert_eq!(
        prelude_results(&out),
        vec![
            "[2] Map{Nat,Nat}: 1 |-> 10, 2 |-> 20", // insert(1,10,insert(2,20,empty))
            "[3] NzNat: 10",                        // (… )[1]
            "[3] NzNat: 20",                        // (… )[2]
            "[1] [Nat]: undefined",                 // (… )[3] — miss → kind-level undefined
            "[1] Bool: true",                       // $hasMapping(…, 1)
            "[1] Bool: false",                      // $hasMapping((1|->10), 3)
        ],
        "MAP ops: {out}"
    );
}

/// Load `ARRAY{Nat, Nat0}` and exercise two-parameter default values for present and missing indices.
#[test]
fn prelude_array_through_repl() {
    let out = repl().eval(conformance_file!("prelude-array.maude")).output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "ARRAY builds: {out}"
    );
    assert_eq!(
        prelude_results(&out),
        vec![
            "[6] Array{Nat,Nat0}: 1 |-> 10 ; 2 |-> 20", // insert(1,10,insert(2,20,empty))
            "[3] NzNat: 10",                            // (… )[1]
            "[1] Zero: 0",                              // (… )[3] — miss → DEFAULT 0
            "[1] Bool: true",                           // $hasMapping((1|->10), 1)
        ],
        "ARRAY ops: {out}"
    );
}

/// Variable aliases are module-local. When an importer and dependency declare the same variable name
/// at different sorts, each equation resolves against its defining module.
#[test]
fn var_shadowing_through_repl() {
    let out = repl().eval(conformance_file!("var-shadowing.maude")).output;
    assert!(
        !out.contains("no parse"),
        "the shadowed prefix application must parse: {out}"
    );
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(
        results,
        vec!["result T: e e", "result T: e", "result S: a"],
        "shadow values: {out}"
    );
}

/// A theory becomes current; `[nonexec]` axioms remain inert while ordinary theory equations execute.
#[test]
fn theory_nonexec_through_repl() {
    let out = repl()
        .eval(conformance_file!("theory-nonexec.maude"))
        .output;
    assert!(out.contains("reduce in ELT-ORD :"), "header: {out}");
    assert!(
        out.contains("result Bool: e < e"),
        "nonexec not applied: {out}"
    );
    assert!(out.contains("result Elt: e"), "exec eq fires: {out}");
    assert!(out.contains("rewrites: 0"), "nonexec count: {out}");
    assert!(out.contains("rewrites: 1"), "exec count: {out}");
}

/// A multi-line theory is buffered as ONE submission by `input_complete` (which recognizes
/// `fth`/`endfth`), then entered and made current — the interactive multi-line boundary for theories.
#[test]
fn theory_entry_is_one_submission_and_current() {
    let mut r = repl();
    assert!(
        !r.input_complete("fth TRIV is\n"),
        "open theory keeps buffering"
    );
    assert!(
        !r.input_complete("fth TRIV is\n  sort Elt .\n"),
        "a `.` inside an open theory is not the end"
    );
    let src = "fth TRIV is\n  sort Elt .\nendfth\n";
    assert!(r.input_complete(src), "`endfth` completes the submission");
    let ev = r.eval(src);
    assert!(!ev.exit);
    assert_eq!(r.current(), Some("TRIV"));
}

/// A view loads through the REPL; the target still reduces and `show views` / `show view` expose it.
#[test]
fn view_through_repl() {
    let mut r = repl();
    let out = r.eval(conformance_file!("view-good.maude")).output;
    assert!(out.contains("result N: z"), "target module reduces: {out}");
    assert!(
        r.eval("show views .").output.contains("ToNum"),
        "show views lists it"
    );
    let shown = r.eval("show view ToNum .").output;
    assert_eq!(
        shown,
        "view ToNum from TRIV to NUM is\n  sort Elt to N .\nendv"
    );
}

/// A parameterized module builds and reduces through the REPL — it echoes as its bare base name
/// (`CTR`, not `CTR{X}`) and its results print with structured sorts (`Ctr{X}` / least sort `NzCtr{X}`).
#[test]
fn parameterized_module_through_repl() {
    let out = repl().eval(conformance_file!("param-module.maude")).output;
    assert!(
        out.contains("reduce in CTR :"),
        "echoes as the base name: {out}"
    );
    assert!(
        out.contains("result Ctr{X}: zero"),
        "structured result sort: {out}"
    );
    assert!(
        out.contains("result NzCtr{X}: inc(inc(zero))"),
        "least sort over structured sorts: {out}"
    );
}

/// Parameterized-module instantiation through the REPL end-to-end — a single-parameter `BOX{ToColor}`
/// (structured instance sort `Box{ToColor}`, view-image sort `Hue`) and a multi-parameter `PR{VA, VB}`.
#[test]
fn instantiation_through_repl() {
    let out = repl().eval(conformance_file!("instantiation.maude")).output;
    assert!(
        out.contains("result Box{ToColor}: wrap(green)"),
        "structured instance sort: {out}"
    );
    assert!(out.contains("result Hue: green"), "view-image sort: {out}");
    assert!(
        out.contains("result SA: a"),
        "multi-parameter instantiation: {out}"
    );
}

/// Chained instantiation `M{ToTheory}{Arg}` binds a parameter to a richer theory, then applies a
/// by-parameter/module view. The chained import renaming collapses the multilevel structured sort:
/// `USE{X :: ORD}` instantiates `LST{ORD}{X}` at `USE{OrdColor}` while renaming `Lst{ORD}{X}` to
/// `Lst{X}`.
#[test]
fn instantiation_chained_through_repl() {
    let out = repl()
        .eval(conformance_file!("instantiation-chained.maude"))
        .output;
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(
        results,
        vec![
            "result Lst{OrdColor}: cons(red, cons(green, nil))", // pair(red, green) — chained instance sort
            "result Lst{OrdColor}: cons(green, nil)",
        ],
        "chained instantiation: {out}"
    );
}

/// View operator maps applied at instantiation through the REPL — `op zero to term f0` (op→term)
/// and `op wrap to box` (op→op), so `ARR{ToFL}`'s `d0`/`d1` reduce to the target's terms.
#[test]
fn view_opmap_through_repl() {
    let out = repl()
        .eval(conformance_file!("param-view-opmap.maude"))
        .output;
    assert!(out.contains("result F: f0"), "op->term: {out}");
    assert!(
        out.contains("result F: box(f0)"),
        "op->op over op->term: {out}"
    );
}

/// A parameter theory that imports a module — the module-declared sort `Bool` is kept (not
/// renamed to `X$Bool`), so the parameterized module builds and the instance reduces.
#[test]
fn theory_module_sorts_through_repl() {
    let out = repl()
        .eval(conformance_file!("param-theory-module-sorts.maude"))
        .output;
    assert!(
        out.contains("result Bool: tt"),
        "module-declared sort kept: {out}"
    );
}

/// Load the BOOL stack and exercise polymorphic expansion, equality and branch hooks, lazy condition
/// selection, stuck-branch normalization, and canonical truth anchors.
#[test]
fn prelude_bool_m0_through_repl() {
    let out = repl().eval(conformance_file!("prelude-bool.maude")).output;
    // The poly ops parse and pretty-print — the headers round-trip the mixfix.
    assert!(
        out.contains("reduce in BOOL : true == true ."),
        "== header: {out}"
    );
    assert!(
        out.contains("reduce in BOOL : if true then false else true fi ."),
        "if header: {out}"
    );
    assert!(
        out.contains("reduce in BOOL : if X:Bool then true and false else true or false fi ."),
        "stuck if header: {out}"
    );
    // Result value + sort, in order.
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(
        results,
        vec![
            "result Bool: false",                             // true and false
            "result Bool: true",                              // true == true
            "result Bool: true",                              // true =/= false
            "result Bool: false",                             // if true then false else true fi
            "result Bool: if X:Bool then false else true fi", // stuck if normalizes both branches
            "result Bool: true",                              // false or true and not false
        ],
        "values: {out}"
    );
    // Distinctive rewrite counts: four single-rewrite reduces, the 5-rewrite stuck conditional, and
    // the 7-rewrite xor expansion.
    assert_eq!(
        out.matches("rewrites: 1\n").count(),
        4,
        "1-rewrite reduces: {out}"
    );
    assert!(out.contains("rewrites: 7\n"), "xor-expansion count: {out}");
    assert!(
        out.contains("rewrites: 5\n"),
        "stuck-branch normalization count: {out}"
    );
}

/// Polymorphic/Universal expansion over two distinct kinds. Equality and conditional operators receive
/// per-kind instances with correct grammar dispatch and non-Bool result sorts.
#[test]
fn poly_multikind_through_repl() {
    let out = repl()
        .eval(conformance_file!("poly-multikind.maude"))
        .output;
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(
        results,
        vec![
            "result Bool: true",  // true == true     (Bool-kind ==)
            "result Bool: false", // true == false    (Bool-kind ==)
            "result Bool: true",  // c0 == c0         (Color-kind ==)
            "result Bool: false", // c0 == c2         (Color-kind ==)
            "result Color: c0",   // if true then c0 else c2 fi          (Color-kind if)
            "result Color: c2",   // if (c1 == c2) then c0 else c2 fi    (nested == then if)
        ],
        "multikind values: {out}"
    );
    // The nested reduce takes two rewrites. Canonical echo removes redundant condition parentheses.
    assert!(
        out.contains("reduce in MK : if c1 == c2 then c0 else c2 fi .")
            && out.contains("rewrites: 2\n"),
        "nested ==/if count: {out}"
    );
}

/// A bare boolean condition abbreviates equality with `true`. The fixture pins both the successful and
/// failed conditional-equation paths, including their rewrite counts.
#[test]
fn bare_condition_through_repl() {
    let out = repl()
        .eval(conformance_file!("bare-condition.maude"))
        .output;
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(
        results,
        vec!["result Foo: b", "result Foo: f(b)"],
        "bare-cond values: {out}"
    );
    // f(a): == eval + eq application = 2; f(b): == eval only (condition false) = 1.
    assert_eq!(
        out.matches("rewrites: 2\n").count(),
        1,
        "fired count: {out}"
    );
    assert_eq!(
        out.matches("rewrites: 1\n").count(),
        1,
        "not-fired count: {out}"
    );
}

/// Load the NAT stack and exercise arithmetic, modular exponentiation, ACU bitwise folds, symmetric
/// difference, shifts, and bignum inputs.
#[test]
fn prelude_nat_through_repl() {
    let out = repl().eval(conformance_file!("prelude-nat.maude")).output;
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(
        results,
        vec![
            "result NzNat: 5",                    // 2 + 3
            "result NzNat: 3",                    // 7 quo 2
            "result NzNat: 1",                    // 7 rem 2
            "result NzNat: 1024",                 // 2 ^ 10
            "result NzNat: 6",                    // gcd(12, 18)
            "result NzNat: 2",  // gcd(12, 18, 8)  — prefix N-ary folds to 1 rewrite
            "result NzNat: 12", // lcm(4, 6)
            "result NzNat: 3",  // min(3, 5)
            "result NzNat: 5",  // max(3, 5)
            "result NzNat: 5",  // sd(3, 8)
            "result NzNat: 5",  // sd(8, 3)  — commutative
            "result NzNat: 6",  // 5 xor 3
            "result Zero: 0",   // 5 xor 5   — multiplicity cancels
            "result NzNat: 8",  // 12 & 10
            "result NzNat: 14", // 12 | 10
            "result NzNat: 24", // modExp(2, 10, 1000)
            "result NzNat: 40", // 5 << 3
            "result NzNat: 18446744073709551616", // 1 << 64  — bignum shift
            "result NzNat: 5",  // 40 >> 3
            "result Bool: true", // 3 < 5
            "result Bool: true", // 5 <= 5
            "result Bool: true", // 7 > 2
            "result Bool: false", // 2 >= 7
            "result Bool: true", // 3 divides 12
        ],
        "NAT values/sorts: {out}"
    );
    // Every reduce here is a single built-in rewrite (2-operand / prefix N-ary).
    assert_eq!(
        out.matches("rewrites: 1\n").count(),
        24,
        "NAT counts: {out}"
    );
}

/// `modExp` reduces any natural base, including one at or above the modulus (the backend's
/// modular power needs a pre-reduced base and used to panic, losing the whole submission's output).
/// Modulus 1 gives 0; a zero modulus is off the `NzNat` domain and stays unreduced.
#[test]
fn prelude_nat_mod_exp_reduces_any_base() {
    let src = format!(
        "{}\nred modExp(9, 1, 4) .\nred modExp(6, 2, 6) .\nred modExp(23, 5, 7) .\n\
         red modExp(18446744073709551621, 2, 1000) .\nred modExp(4, 0, 1) .\n\
         red modExp(5, 3, 0) .\n",
        conformance_file!("prelude-nat.maude")
    );
    let out = repl().eval(&src).output;
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(
        results[results.len() - 6..],
        [
            "result NzNat: 1",   // 9 ≡ 1 (mod 4)
            "result Zero: 0",    // base == modulus
            "result NzNat: 4",   // 23 ≡ 2, 2^5 = 32 ≡ 4 (mod 7)
            "result NzNat: 641", // 2^64 + 5 ≡ 621, 621^2 ≡ 641 (mod 1000)
            "result Zero: 0",    // modulus 1, even for x^0
            "result [Nat]: modExp(5, 3, 0)",
        ],
        "{out}"
    );
    // The fixture's 24 one-rewrite reductions plus the five reducing `modExp`s above.
    assert_eq!(out.matches("rewrites: 1\n").count(), 24 + 5, "{out}");
}

/// Tier 2 — the remaining built-in data types + leaf special ops: INT (`abs`/`~`, signed bignum +
/// two's-complement bitwise), RAT (rationals on the Division op), FLOAT (full op set + partiality:
/// `/0`/NaN don't reduce, but `log(0.0) = -Infinity` does), STRING/QID (`ascii`/`char`/`find`/case +
/// STRING-OPS classification/trim; value-dependent `Char`/`String` sort; qid backquote-escaping),
/// CONVERSION (float↔rat↔string + `decFloat`), INITIAL-EQUALITY-PREDICATE, RANDOM (MT19937 seed 0),
/// COUNTER (stateful — inert under `reduce`, advancing under `rewrite`). One fixture exercises the
/// complete chain through module-qualified reductions.
#[test]
fn prelude_tier2_through_repl() {
    let out = repl().eval(conformance_file!("prelude-tier2.maude")).output;
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(
        results,
        vec![
            // INT — abs, ~, (-1)&12, (-5) xor 3, -7 quo 2, (-3)*(-4), gcd(-12,18)
            "result NzNat: 5",
            "result NzInt: -6",
            "result NzNat: 12",
            "result NzInt: -8",
            "result NzInt: -3",
            "result NzNat: 12",
            "result NzNat: 6",
            // RAT
            "result PosRat: 5/6",
            "result PosRat: 2/3",
            "result PosRat: 3/4",
            "result NzNat: 3",
            // FLOAT — 2^10, sqrt 2, floor 3.7, atan2; then partiality: /0 and sqrt(-1) stay [Float],
            // log(0) = -Infinity; `=[ ]` approx-equality
            "result FiniteFloat: 1.024e+3",
            "result FiniteFloat: 1.4142135623730951",
            "result FiniteFloat: 3.0",
            "result FiniteFloat: 7.8539816339744828e-1",
            "result [Float]: 1.0 / 0.0",
            "result [Float]: sqrt(-1.0)",
            "result Float: -Infinity",
            "result Bool: true",
            // STRING — concat, ascii, char, find, rfind, upperCase (Char vs String sort is value-dependent)
            "result String: \"foobar\"",
            "result NzNat: 65",
            "result Char: \"A\"",
            "result NzNat: 2",
            "result NzNat: 2",
            "result String: \"HELLO\"",
            // STRING-OPS — isDigit, isAlphabetic, startsWith, trim
            "result Bool: true",
            "result Bool: true",
            "result Bool: true",
            "result String: \"hi\"",
            // QID — string('foo); qid("a b") escapes the space as a backquote
            "result String: \"foo\"",
            "result Qid: 'a`b",
            // CONVERSION — float, rat (exact), string-in-base, rat-from-base, float→string, string→float,
            // decFloat
            "result FiniteFloat: 5.0e-1",
            "result PosRat: 3602879701896397/36028797018963968",
            "result String: \"ff\"",
            "result NzNat: 255",
            "result String: \"-2.75\"",
            "result FiniteFloat: 3.1400000000000001",
            "result DecFloat: < 1, \"123456\", 3 >",
            // INITIAL-EQUALITY-PREDICATE, RANDOM, COUNTER (reduce leaves it; rewrite below advances it)
            "result Bool: true",
            "result NzNat: 2357136044",
            "result NzNat: 2774094101",
            "result [Nat]: counter",
            "result NzNat: 3",
        ],
        "Tier 2 values/sorts: {out}"
    );
    // COUNTER under `rewrite` yields 0, 1, 2 → 0 + 1 + 2 = 3 in 5 rewrites (3 counter steps + 2 ACU
    // folds) — the only multi-rewrite command here (the kind-sorted `[Float]`/`counter` results above
    // already attest the partial-op / inert-counter non-reductions).
    assert!(
        out.contains("rewrite in COUNTER :") && out.contains("rewrites: 5\n"),
        "counter: {out}"
    );
}

/// Under META descent, each `CounterSymbol` operator of the reflected module counts from 0 on its
/// own (manual §16.1), for `metaRewrite` and `metaFrewrite`, and every call starts again from 0.
#[test]
fn meta_rewrite_counter_operators_are_independent() {
    let mut r = repl();
    r.eval(conformance_file!("prelude-meta.maude"));
    let out = r
        .eval(concat!(
            "mod META-COUNTERS is\n",
            "  protecting NAT .\n",
            "  sort Seq .\n",
            "  subsort Nat < Seq .\n",
            "  op _;_ : Seq Seq -> Seq [assoc] .\n",
            "  op up : -> [Nat] [special (id-hook CounterSymbol op-hook succSymbol (s_ : Nat ~> NzNat))] .\n",
            "  op dn : -> [Nat] [special (id-hook CounterSymbol op-hook succSymbol (s_ : Nat ~> NzNat))] .\n",
            "endm\n",
            "red in META-LEVEL : metaRewrite(['META-COUNTERS], '_;_['up.Nat, 'dn.Nat, 'up.Nat], 3) .\n",
            "red in META-LEVEL : metaRewrite(['META-COUNTERS], '_;_['up.Nat, 'dn.Nat, 'up.Nat], 3) .\n",
            "red in META-LEVEL : metaFrewrite(['META-COUNTERS], '_;_['dn.Nat, 'up.Nat, 'dn.Nat], 3, 1) .\n",
        ))
        .output;
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(
        results, ["result ResultPair: {'_;_['0.Zero, '0.Zero, 's_['0.Zero]], 'Seq}"; 3],
        "{out}"
    );
}

/// TNK-BUILTIN-001: the kind-level `I / 0` left by the division built-in is not a rational, so
/// `float` and `string` of it stay unreduced (they used to panic, or render an invented `"3/0"`).
/// Likewise `rat` of a string whose denominator is negative falls through instead of dropping the
/// sign (`"3/-2"` gave `3/2`).
#[test]
fn conversion_of_non_rational_division_falls_through() {
    let src = format!(
        "{}\nred in CONVERSION : float(-7 / (2 - 2)) .\nred in CONVERSION : float(0 / 0) .\n\
         red in CONVERSION : string(3 / 0, 10) .\nred in CONVERSION : rat(\"3/-2\", 10) .\n\
         red in CONVERSION : rat(\"-ff/-10\", 16) .\nred in CONVERSION : float(1 / 4) .\n\
         red in CONVERSION : string(-3 / 4, 2) .\nred in CONVERSION : rat(\"-3/2\", 10) .\n",
        conformance_file!("prelude-tier2.maude")
    );
    let out = repl().eval(&src).output;
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(
        results[results.len() - 8..],
        [
            "result [Float]: float(-7 / 0)",
            "result [Float]: float(0 / 0)",
            "result [String]: string(3 / 0, 10)",
            "result [Rat,FindResult]: rat(\"3/-2\", 10)",
            "result [Rat,FindResult]: rat(\"-ff/-10\", 16)",
            // Controls: proper rationals still convert.
            "result FiniteFloat: 2.5e-1",
            "result String: \"-11/100\"",
            "result NzRat: -3/2",
        ],
        "{out}"
    );
}

/// `find`, `rfind`, and `substr` are total, so an index or count of `2^64` or more is past the end
/// like any other (they stayed unreduced, and `find(..) == notFound` was `false`). The partial `char`
/// still leaves an out-of-range code unreduced.
#[test]
fn string_index_past_machine_width_through_repl() {
    let src = format!(
        "{}\nred in STRING : find(\"pqrpqr\", \"qr\", 18446744073709551616) .\n\
         red in STRING : rfind(\"pqrpqr\", \"qr\", 98765432109876543210987) .\n\
         red in STRING : substr(\"lmnopq\", 3, 18446744073709551616) .\n\
         red in STRING : substr(\"lmnopq\", 18446744073709551616, 3) .\n\
         red in STRING : find(\"pqr\", \"\", 18446744073709551616) .\n\
         red in STRING : rfind(\"pqr\", \"\", 18446744073709551616) .\n\
         red in STRING : find(\"pqrpqr\", \"qr\", 18446744073709551616) == notFound .\n\
         red in STRING : char(18446744073709551616) .\n",
        conformance_file!("prelude-tier2.maude")
    );
    let out = repl().eval(&src).output;
    let lines: Vec<&str> = out
        .lines()
        .filter(|l| l.starts_with("rewrites: ") || l.starts_with("result "))
        .collect();
    assert_eq!(
        lines[lines.len() - 16..],
        [
            "rewrites: 1",
            "result FindResult: notFound",
            "rewrites: 1",
            "result NzNat: 4", // the last occurrence
            "rewrites: 1",
            "result String: \"opq\"",
            "rewrites: 1",
            "result String: \"\"",
            "rewrites: 1",
            "result FindResult: notFound", // as for any start past the end
            "rewrites: 1",
            "result NzNat: 3",
            "rewrites: 2",
            "result Bool: true",
            "rewrites: 0",
            "result [String]: char(18446744073709551616)",
        ],
        "{out}"
    );
}

/// `_^_`, `_<<_`, and `_>>_` reduce for counts of `2^64` or more whenever the exact result is small:
/// bases `0` and `±1`, `0 << k`, and `x >> k` (`0`, or `-1` below zero). They used to stay unreduced,
/// so `1 ^ k == 1` was `false`. A nonzero left shift or other base that far still stays unreduced,
/// and a negative count is off the `Nat` domain: `7 >> -1` stays unreduced instead of giving `3`.
#[test]
fn int_pow_and_shift_counts_past_u64_through_repl() {
    let src = format!(
        "{}\nred in INT : 1 ^ 18446744073709551616 .\nred in INT : -1 ^ 18446744073709551616 .\n\
         red in INT : -1 ^ 55340232221128654849 .\nred in INT : 0 ^ 55340232221128654849 .\n\
         red in INT : 0 << 18446744073709551616 .\nred in INT : 7 >> 18446744073709551616 .\n\
         red in INT : -7 >> 55340232221128654849 .\nred in INT : 1 ^ 18446744073709551616 == 1 .\n\
         red in INT : 2 ^ 18446744073709551616 .\nred in INT : -3 << 18446744073709551616 .\n\
         red in INT : 7 >> -1 .\nred in INT : 7 << -1 .\nred in INT : 0 << -18446744073709551616 .\n",
        conformance_file!("prelude-tier2.maude")
    );
    let out = repl().eval(&src).output;
    let lines: Vec<&str> = out
        .lines()
        .filter(|l| l.starts_with("rewrites: ") || l.starts_with("result "))
        .collect();
    assert_eq!(
        lines[lines.len() - 26..],
        [
            "rewrites: 1",
            "result NzNat: 1",
            "rewrites: 1",
            "result NzNat: 1", // even exponent
            "rewrites: 1",
            "result NzInt: -1", // odd exponent
            "rewrites: 1",
            "result Zero: 0",
            "rewrites: 1",
            "result Zero: 0",
            "rewrites: 1",
            "result Zero: 0",
            "rewrites: 1",
            "result NzInt: -1", // floors toward -infinity
            "rewrites: 2",
            "result Bool: true",
            "rewrites: 0",
            "result NzNat: 2 ^ 18446744073709551616",
            "rewrites: 0",
            "result Int: -3 << 18446744073709551616",
            "rewrites: 0",
            "result [Int]: 7 >> -1",
            "rewrites: 0",
            "result [Int]: 7 << -1",
            "rewrites: 0",
            "result [Int]: 0 << -18446744073709551616",
        ],
        "{out}"
    );
}

/// A machine-word exponent whose result size `bits(|base|) · e` overflows `u64` (a power of more
/// than `2^63` bits) stays unreduced. The backend's unchecked size arithmetic used to wrap:
/// `2 ^ 2^63` reduced to `1`, `7 ^ 6148914691236517206` panicked, and `3 ^ (2^64 - 1)` aborted,
/// losing the whole submission's output.
#[test]
fn pow_result_size_overflow_stays_unreduced_through_repl() {
    let src = format!(
        "{}\nred in NAT : 2 ^ 9223372036854775808 .\nred in INT : -2 ^ 9223372036854775809 .\n\
         red in NAT : 7 ^ 6148914691236517206 .\nred in NAT : 3 ^ 18446744073709551615 .\n\
         red in NAT : 2 ^ 64 .\n",
        conformance_file!("prelude-tier2.maude")
    );
    let out = repl().eval(&src).output;
    let lines: Vec<&str> = out
        .lines()
        .filter(|l| l.starts_with("rewrites: ") || l.starts_with("result "))
        .collect();
    assert_eq!(
        lines[lines.len() - 10..],
        [
            "rewrites: 0",
            "result NzNat: 2 ^ 9223372036854775808",
            "rewrites: 0",
            "result NzInt: -2 ^ 9223372036854775809",
            "rewrites: 0",
            "result NzNat: 7 ^ 6148914691236517206",
            "rewrites: 0",
            "result NzNat: 3 ^ 18446744073709551615",
            "rewrites: 1",
            "result NzNat: 18446744073709551616", // an ordinary power still reduces
        ],
        "{out}"
    );
}

/// Parameterized views compose with structured-sort renamings during module instantiation. This case
/// combines `view V{X :: T} from T to M{X}` with `* (sort Box{ColorE} to ColorBox)`; the instantiated
/// module builds and reduces. Chained multilevel instantiation is covered separately by
/// [`instantiation_chained_through_repl`].
#[test]
fn view_parameterized_through_repl() {
    let out = repl()
        .eval(conformance_file!("view-parameterized.maude"))
        .output;
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(
        results,
        vec![
            "result ColorBox: b(red, green)", // b(red, green)
            "result ColorBox: b(red, green)", // b(green, red) — comm, same canonical form
        ],
        "parameterized-view instantiation + structured renaming: {out}"
    );
}

/// The eq parser splits a statement body at the **last** top-level `=` and peels a trailing `[attrs]`
/// only when its first inner token is an attribute keyword — so an equation with a `[_]`-list rhs
/// (`eq rev([X] L) = rev(L) [X] .`) keeps its bracketed term, and one ending in `[owise]` is still
/// recognised as an owise equation. The separator-aware rule is required by the `[_]`-list modules
/// `LIST*`/`SET*`; an `=[` inside `_=[_]_` must not cause a later `= [` separator to be skipped.
#[test]
fn eq_bracket_rhs_through_repl() {
    let out = repl()
        .eval(conformance_file!("eq-bracket-rhs.maude"))
        .output;
    let results: Vec<&str> = out.lines().filter(|l| l.starts_with("result ")).collect();
    assert_eq!(
        results,
        vec![
            "result BList: [c] [b] [a]", // rev([a] [b] [c]) — `[X]`-rhs equation
            "result Elt: a",             // headOr([a] [b], c) — `[X] L` pattern matches
            "result Elt: c",             // headOr(nil, c) — falls to the `[owise]` equation
        ],
        "`[_]`-list rhs + `[owise]` peel: {out}"
    );
}

/// A view buffers as one submission via `view`/`endv`; a missing target sort reports a friendly error
/// without panicking or aborting the session.
#[test]
fn bad_view_reports_error_through_repl() {
    let mut r = repl();
    assert!(
        !r.input_complete("view V from TRIV to NUM is\n"),
        "open view keeps buffering"
    );
    assert!(
        r.input_complete("view V from TRIV to NUM is endv\n"),
        "`endv` completes the submission"
    );
    r.eval("fth TRIV is sort Elt . endfth");
    r.eval("fmod NUM is sort N . endfm");
    let out = r
        .eval("view Bad from TRIV to NUM is sort Elt to NoSuch . endv")
        .output;
    assert!(
        out.contains("failed to find sort NoSuch in NUM"),
        "got: {out}"
    );
    // The session survives — a following module still enters.
    r.eval("fmod OK is sort Z . endfm");
    assert_eq!(r.current(), Some("OK"));
}

/// Structure sharing through the REPL reduces a repeated subterm once. Fixture counts top out at two;
/// any `rewrites: 3` or `rewrites: 4` record exposes an over-count.
#[test]
fn sharing_through_repl() {
    let out = repl()
        .eval(conformance_file!("correctness-sharing.maude"))
        .output;
    assert!(
        out.contains("result P: < c, c >"),
        "deep shared chain: {out}"
    );
    assert!(
        out.contains("result P: < b, b >"),
        "free/rhs/triple dup: {out}"
    );
    assert!(
        out.contains("result P: < mkA, mkA >"),
        "mb on shared constant: {out}"
    );
    assert!(out.contains("result L: b b b"), "AU triple share: {out}");
    assert!(out.contains("result E: b & b"), "CUI share: {out}");
    assert!(out.contains("result E: b + b"), "ACU share: {out}");
    assert!(
        !out.contains("rewrites: 3"),
        "no sharing over-count (f(a) was 3): {out}"
    );
    assert!(
        !out.contains("rewrites: 4"),
        "no sharing over-count (chain/triple were 4): {out}"
    );
}

/// A long result is wrapped to 79 columns with four-space continuation indentation. This pins
/// end-to-end wrapping while ensuring short output remains untouched.
#[test]
fn long_result_is_line_wrapped() {
    let mut r = repl();
    r.eval("fmod W is sort N . op z : -> N [ctor] . op s_ : N -> N [ctor] . endfm");
    let out = r.eval(&format!("red {}z .", "s ".repeat(40))).output;
    assert!(
        out.contains("\n    s"),
        "a wrapped continuation line carries the 4-space indent: {out}"
    );
    for line in out.lines() {
        assert!(
            line.len() <= 79,
            "every line stays within 79 columns: {} cols in {line:?}",
            line.len()
        );
    }
    // A short reduction is unaffected (no wrapping introduced).
    let short = r.eval("red s s z .").output;
    assert!(
        short.contains("result N: s s z"),
        "short result rendered: {short}"
    );
    assert!(
        !short.contains("\n    "),
        "short result is not wrapped: {short}"
    );
}

/// The `match` command renders solutions (a commutative pattern → two pairings).
#[test]
fn match_command_through_repl() {
    let mut r = repl();
    r.eval("fmod M is sort E . ops a b : -> E . op g : E E -> E [comm] . vars X Y : E . endfm");
    let out = r.eval("match g(X, Y) <=? g(a, b) .").output;
    assert!(out.contains("match in M :"), "header: {out}");
    assert!(
        out.contains("X --> a") && out.contains("X --> b"),
        "pairings: {out}"
    );
}

/// `select` switches the current module; success is silent, an unknown module is reported.
#[test]
fn select_and_show() {
    let mut r = repl();
    r.eval("fmod A is sort SA . op a : -> SA [ctor] . endfm");
    r.eval("fmod B is sort SB . op b : -> SB [ctor] . endfm");
    assert_eq!(r.current(), Some("B"));

    assert!(
        r.eval("select A .").output.is_empty(),
        "select success is silent"
    );
    assert_eq!(r.current(), Some("A"));
    assert!(r.eval("select NOPE .").output.contains("no module"));

    let mods = r.eval("show modules .").output;
    assert!(
        mods.contains('A') && mods.contains('B'),
        "show modules: {mods}"
    );
    let sm = r.eval("show module .").output; // current = A
    assert!(
        sm.contains("fmod A") && sm.contains("SA"),
        "show module: {sm}"
    );
}

/// `quit`/`q`/`exit` signal exit.
#[test]
fn quit_exits() {
    let mut r = repl();
    assert!(r.eval("quit").exit);
    assert!(r.eval("q").exit);
    assert!(r.eval("exit").exit);
    assert!(!r.eval("red x .").exit);
}

/// An undefined import is reported (the REPL doesn't crash).
#[test]
fn unknown_import_reported() {
    let out = repl()
        .eval("fmod M is protecting NOPE . sort S . endfm")
        .output;
    assert!(
        out.contains("not defined") || out.contains("error"),
        "got: {out}"
    );
}

/// Peano naturals with prefix successor and infix addition.
const PEANO: &str = "fmod PEANO is sort Nat . op 0 : -> Nat [ctor] . op s_ : Nat -> Nat [ctor] . \
     op _+_ : Nat Nat -> Nat . vars N M : Nat . eq N + 0 = N . eq N + s M = s (N + M) . endfm";

/// `set trace on` prints each rewrite step; `set trace off` removes them.
#[test]
fn trace_shows_rewrite_steps() {
    let mut r = repl();
    r.eval(
        "fmod NAT0 is sort N . op 0 : -> N [ctor] . op s : N -> N [ctor] . op add : N N -> N . \
         vars X Y : N . eq add(0, Y) = Y . eq add(s(X), Y) = s(add(X, Y)) . endfm",
    );
    r.eval("set trace on .");
    let out = r.eval("red add(s(0), s(0)) .").output;
    assert_eq!(
        out.matches("*********** equation").count(),
        2,
        "two steps: {out}"
    );
    assert!(out.contains("add(s(0), s(0))\n--->"), "first redex: {out}");
    assert!(out.contains("result N: s(s(0))"), "result: {out}");

    r.eval("set trace off .");
    let plain = r.eval("red add(s(0), s(0)) .").output;
    assert!(!plain.contains("***********"), "no trace when off: {plain}");
}

/// The full equation trace orders the body, substitution, redex, and result.
#[test]
fn trace_full_equation_block() {
    let mut r = repl();
    r.eval(PEANO);
    r.eval("set trace on .");
    let out = r.eval("red s 0 + s 0 .").output;
    assert!(
        out.contains(
            "*********** equation\n\
             eq N + s M = s (N + M) .\n\
             N --> s 0\n\
             M --> 0\n\
             s 0 + s 0\n\
             --->\n\
             s (s 0 + 0)\n\
             *********** equation\n\
             eq N + 0 = N .\n\
             N --> s 0\n\
             s 0 + 0\n\
             --->\n\
             s 0\n"
        ),
        "full eq trace block:\n{out}"
    );
}

/// `set trace substitution off` drops the `Var --> binding` lines; `set trace whole on` adds the
/// `Old:`/`New:` whole-term lines (the inner step's whole is the *full* term, not just the redex).
#[test]
fn trace_substitution_and_whole_flags() {
    let mut r = repl();
    r.eval(PEANO);
    r.eval("set trace on .");
    r.eval("set trace substitution off .");
    let no_subst = r.eval("red s 0 + s 0 .").output;
    assert!(
        no_subst.contains("*********** equation\neq N + s M = s (N + M) .\ns 0 + s 0\n--->"),
        "no subst: {no_subst}"
    );
    // The substitution `Var --> binding` lines are gone (the `--->` arrow is not a substitution line).
    assert!(
        !no_subst.contains("N --> ") && !no_subst.contains("M --> "),
        "substitution lines dropped: {no_subst}"
    );

    r.eval("set trace substitution on .");
    r.eval("set trace whole on .");
    let whole = r.eval("red s 0 + s 0 .").output;
    // The second (inner) step rewrites `s 0 + 0`; its whole term is `s (s 0 + 0)` -> `s s 0`.
    assert!(
        whole.contains("Old: s (s 0 + 0)\ns 0 + 0\n--->\ns 0\nNew: s s 0\n"),
        "whole inner step: {whole}"
    );
}

/// A conditional equation traces the whole sub-stream: `trial #1`, the `ceq … if …` body + the
/// substitution, `solving`/`success for condition fragment`, and `success #1`, then the firing step.
#[test]
fn trace_conditional_substream() {
    let mut r = repl();
    r.eval(
        "fmod CEQ-MAX is sorts Nat Truth . ops tt ff : -> Truth [ctor] . op z : -> Nat [ctor] . \
         op s_ : Nat -> Nat [ctor] . op _<=_ : Nat Nat -> Truth . op max : Nat Nat -> Nat . \
         vars M N : Nat . eq z <= N = tt . eq s M <= z = ff . eq s M <= s N = M <= N . \
         ceq max(M, N) = N if M <= N = tt . ceq max(M, N) = M if M <= N = ff . endfm",
    );
    r.eval("set trace on .");
    let out = r.eval("red max(s z, s s z) .").output;
    assert!(
        out.contains(
            "*********** trial #1\n\
             ceq max(M, N) = N if M <= N = tt .\n\
             M --> s z\n\
             N --> s s z\n\
             *********** solving condition fragment\n\
             M <= N = tt\n"
        ),
        "trial + fragment start:\n{out}"
    );
    assert!(
        out.contains(
            "*********** success for condition fragment\n\
             M <= N = tt\n\
             M --> s z\n\
             N --> s s z\n\
             *********** success #1\n"
        ),
        "fragment success + trial success:\n{out}"
    );
    assert!(out.contains("result Nat: s s z"), "result: {out}");
}

/// `set trace condition off` keeps the trial/fragment scaffolding but hides the condition's nested
/// reductions (the `s z <= s s z` equation steps); a failed-then-backtracked trial renders `failure #1`.
#[test]
fn trace_condition_off_and_backtrack() {
    let mut r = repl();
    r.eval(
        "fmod CEQ-MAX is sorts Nat Truth . ops tt ff : -> Truth [ctor] . op z : -> Nat [ctor] . \
         op s_ : Nat -> Nat [ctor] . op _<=_ : Nat Nat -> Truth . op max : Nat Nat -> Nat . \
         vars M N : Nat . eq z <= N = tt . eq s M <= z = ff . eq s M <= s N = M <= N . \
         ceq max(M, N) = N if M <= N = tt . ceq max(M, N) = M if M <= N = ff . endfm",
    );
    r.eval("set trace on .");
    // Backtrack: trial #1 (first ceq) fails, trial #2 (second ceq) succeeds.
    let bt = r.eval("red max(s s z, s z) .").output;
    assert!(
        bt.contains(
            "*********** failure for condition fragment\nM <= N = tt\n*********** failure #1\n"
        ),
        "failure: {bt}"
    );
    assert!(
        bt.contains("*********** trial #2\nceq max(M, N) = M if M <= N = ff ."),
        "trial #2: {bt}"
    );

    // condition off: the nested `_<=_` equation steps inside the condition disappear, scaffolding stays.
    r.eval("set trace condition off .");
    let off = r.eval("red max(s z, s s z) .").output;
    assert!(off.contains("*********** solving condition fragment\nM <= N = tt\n*********** success for condition fragment"), "scaffolding kept: {off}");
    assert!(
        !off.contains("z <= s z\n--->"),
        "nested condition rewrites hidden: {off}"
    );
}

/// Membership traces show sort narrowing, substitutions, and source/target sorts. Conditional memberships
/// retain their statement body; `set trace whole on` includes the reconstructed root in a `Whole:` line.
#[test]
fn trace_membership_and_cmb() {
    let mut r = repl();
    r.eval(
        "fmod MB-CHAIN is sorts A B C . subsorts C < B < A . op a : -> A [ctor] . op g : A -> A [ctor] . \
         var X : A . mb g(X) : B . mb g(g(X)) : C . endfm",
    );
    r.eval("set trace on .");
    let out = r.eval("red g(g(a)) .").output;
    assert!(
        out.contains("*********** membership axiom\nmb g(X) : B .\nX --> a\nA: g(a) becomes B\n"),
        "inner mb: {out}"
    );
    assert!(
        out.contains(
            "*********** membership axiom\nmb g(g(X)) : C .\nX --> a\nA: g(g(a)) becomes C\n"
        ),
        "outer mb: {out}"
    );
    assert!(out.contains("result C:"), "result sort C: {out}");

    // `set trace whole on` adds the `Whole:` line — the full root term (`g(g(a))`) at each membership
    // application, for both the inner (`g(a) becomes B`) and outer (`g(g(a)) becomes C`) steps.
    r.eval("set trace whole on .");
    let whole = r.eval("red g(g(a)) .").output;
    assert!(
        whole.contains("X --> a\nWhole: g(g(a))\nA: g(a) becomes B\n"),
        "inner mb Whole: {whole}"
    );
    assert!(
        whole.contains("X --> a\nWhole: g(g(a))\nA: g(g(a)) becomes C\n"),
        "outer mb Whole: {whole}"
    );
}

/// Command echoes omit spaces before commas and brackets and after opening brackets, keeping nested terms
/// compact and reparsable.
#[test]
fn command_echo_spacing() {
    let mut r = repl();
    r.eval(
        "fmod E is sorts N P . op z : -> N [ctor] . op s_ : N -> N [ctor] . op g : N -> N . \
         op <_,_> : N N -> P [ctor] . var X : N . eq g(X) = X . endfm",
    );
    let nested = r.eval("red g(g(z)) .").output;
    assert!(
        nested.contains("reduce in E : g(g(z)) ."),
        "nested-paren echo: {nested}"
    );
    let comma = r.eval("red < z, s z > .").output;
    assert!(
        comma.contains("reduce in E : < z, s z > ."),
        "comma echo: {comma}"
    );
}

/// Command echo normalizes and pretty-prints the parsed term, so float, rational, and negative-integer
/// constants use canonical surface forms.
#[test]
fn special_constant_echo_is_canonical() {
    // Float echoes use canonical scientific notation (`100.0` becomes `1.0e+2`).
    let mut r = repl();
    r.eval(conformance_file!("correctness-float-print.maude"));
    let e = r.eval("red 100.0 * 100.0 .").output;
    assert!(
        e.contains("reduce in FLTB : 1.0e+2 * 1.0e+2 ."),
        "float echo: {e}"
    );
    assert!(e.contains("result Flt: 1.0e+4"), "float result: {e}");

    // A rational echo is the compact `num/den`; a `0/N` (Zero numerator) is not a rational, so it
    // stays spaced.
    let mut r = repl();
    r.eval(conformance_file!("rat.maude"));
    let q = r.eval("red 6 / 4 .").output;
    assert!(q.contains("reduce in RATB : 6/4 ."), "rational echo: {q}");
    assert!(q.contains("result NzRat: 3/2"), "rational result: {q}");
    let z = r.eval("red 0 / 5 .").output;
    assert!(
        z.contains("reduce in RATB : 0 / 5 ."),
        "0/N stays spaced: {z}"
    );

    // Glued and spaced negative numerals echo compactly; `5 -7` remains an invalid subtraction form.
    let mut r = repl();
    r.eval(conformance_file!("correctness-glued-minus.maude"));
    let g = r.eval("red -7 quo 2 .").output;
    assert!(
        g.contains("reduce in INTB : -7 quo 2 ."),
        "glued-minus echo: {g}"
    );
    assert!(g.contains("result NzInt: -3"), "glued-minus result: {g}");
    let s = r.eval("red - 3 .").output;
    assert!(
        s.contains("reduce in INTB : -3 ."),
        "spaced minus echoes compact: {s}"
    );
    let bad = r.eval("red 5 -7 .").output;
    assert!(bad.contains("no parse"), "`5 -7` is rejected: {bad}");
}

/// Backtracking through a deterministic `:=` condition fragment revisits that fragment after an
/// earlier matching fragment is re-solved. This affects trace events, not the result or rewrite count.
#[test]
fn trace_multi_fragment_backtrack_resolves_deterministic() {
    let mut r = repl();
    r.eval(
        "fmod BT is sorts E R B . ops a b c : -> E [ctor] . op _;_ : E E -> E [assoc] . \
         op f : E -> E . op g : E -> R . op ok : -> R [ctor] . ops tt ff : -> B [ctor] . \
         op test : E -> B . vars X Y Z : E . eq g(X) = ok . eq test(c) = tt . \
         ceq f(Z) = Y if X ; Y := Z /\\ g(X) = ok /\\ test(Y) = tt . endfm",
    );
    r.eval("set trace on .");
    let out = r.eval("red f(a ; b ; c) .").output;
    // The split `(a, b c)` passes `g(X) = ok` but fails `test(b c) = tt`, so backtracking revisits the
    // deterministic `g(X) = ok` fragment and records its failure.
    assert!(
        out.contains(
            "*********** re-solving condition fragment\n\
             g(X) = ok\n\
             *********** failure for condition fragment\n\
             g(X) = ok\n"
        ),
        "deterministic re-solve on backtrack:\n{out}"
    );
    assert!(
        out.contains("result E: c"),
        "result (a ; b -> X, c -> Y): {out}"
    );
}

/// Drive a multi-submission session the way the binary's stdin loop does (main.rs): buffer lines until
/// `input_complete`, then `eval` each submission. Returns the concatenated output.
fn run_session(input: &str) -> String {
    let mut r = repl();
    let mut out = String::new();
    let mut buffer = String::new();
    for line in input.lines() {
        buffer.push_str(line);
        buffer.push('\n');
        if r.input_complete(&buffer) {
            let ev = r.eval(&buffer);
            buffer.clear();
            if !ev.output.is_empty() {
                out.push_str(&ev.output);
                out.push('\n');
            }
            if ev.exit {
                break;
            }
        }
    }
    out
}

/// The trace fixtures load through the REPL's stdin loop and exercise equation, built-in, membership,
/// and conditional trace streams.
#[test]
fn trace_fixtures_run_through_repl() {
    let eq = run_session(conformance_file!("trace-eq.maude"));
    assert!(
        eq.contains(
            "*********** equation\neq N + s M = s (N + M) .\nN --> s 0\nM --> 0\ns 0 + s 0\n--->\ns (s 0 + 0)\n"
        ),
        "trace-eq:\n{eq}"
    );

    let bi = run_session(conformance_file!("trace-builtin.maude"));
    assert!(
        bi.contains("(built-in equation for symbol _+_)\n2 + 3\n--->\n5\n"),
        "trace-builtin:\n{bi}"
    );

    let mb = run_session(conformance_file!("trace-membership.maude"));
    assert!(
        mb.contains("*********** membership axiom\nmb g(X) : B .\nX --> a\nA: g(a) becomes B\n"),
        "trace-membership:\n{mb}"
    );

    let cond = run_session(conformance_file!("trace-conditional.maude"));
    assert!(
        cond.contains("*********** trial #1\nceq max(M, N) = N if M <= N = tt ."),
        "trial #1:\n{cond}"
    );
    assert!(
        cond.contains("*********** failure #1") && cond.contains("*********** trial #2"),
        "backtrack #1->#2:\n{cond}"
    );
}

/// Collapse-membership traces preserve the source statement, identity binding, and whole-subject line.
#[test]
fn collapsing_membership_fixture_through_repl() {
    let out = repl()
        .eval(conformance_file!("audit/B3c-membership-collapse.maude"))
        .output;
    assert!(
        out.contains(
            "reduce in B3C-DOWNSTREAM-VALUE : wrap(a) .\n\
             rewrites: 2\n\
             result E: b"
        ),
        "downstream sorted equation:\n{out}"
    );
    assert!(
        out.contains(
            "*********** membership axiom\n\
             mb a * X : Special .\n\
             X --> z\n\
             Whole: a\n\
             E: a becomes Special"
        ),
        "collapsed membership trace:\n{out}"
    );
}

/// `rewrite` and `continue` enforce bounds, traverse top-down, and reset rewrite counts on resume.
#[test]
fn rewrite_command_through_repl() {
    let out = repl().eval(conformance_file!("rewrite.maude")).output;
    assert!(
        out.contains("rewrite in CHAIN : a .\nrewrites: 3\nresult S: d"),
        "rewrite a:\n{out}"
    );
    assert!(
        out.contains("rewrite [2] in CHAIN : a .\nrewrites: 2\nresult S: c"),
        "rewrite [2] a:\n{out}"
    );
    assert!(
        out.contains("rewrite in CHAIN : f(a) .\nrewrites: 7\nresult S: d"),
        "rewrite f(a) (7 steps):\n{out}"
    );
    // `rewrite [1] a .` -> b, then `continue 1 .` -> c (count reset to the 1 step done in the continue).
    assert!(
        out.contains(
            "rewrite [1] in CHAIN : a .\nrewrites: 1\nresult S: b\nrewrites: 1\nresult S: c"
        ),
        "[1] then continue:\n{out}"
    );
}

/// `set trace on` with `rewrite` renders a `*********** rule` header, the rule body, the substitution,
/// and the `redex ---> result` tail.
#[test]
fn traced_rewrite_renders_rule_blocks() {
    let s = run_session(
        "mod CHAIN is sort S . ops a b c d : -> S . rl a => b . rl b => c . endm\n\
         set trace on .\n\
         rewrite a .",
    );
    assert!(
        s.contains("*********** rule\nrl a => b .\nempty substitution\na\n--->\nb"),
        "rule block 1:\n{s}"
    );
    assert!(
        s.contains("*********** rule\nrl b => c .\nempty substitution\nb\n--->\nc"),
        "rule block 2:\n{s}"
    );
    assert!(s.contains("rewrites: 2\nresult S: c"), "tail:\n{s}");
}

/// Position-fair `frewrite` differs from greedy `rewrite`, respects frozen arguments, and reports bounded
/// non-normal results without a calculated sort.
#[test]
fn frewrite_command_through_repl() {
    let out = repl().eval(conformance_file!("frewrite.maude")).output;
    // Unbounded: all three positions reach `d` in 9 steps.
    assert!(
        out.contains("frewrite in FR : (a | a) | a .\nrewrites: 9\nresult S: (d | d) | d"),
        "unbounded:\n{out}"
    );
    // Fairness: greedy `rewrite [2]` drains one position; fair `frewrite [2]` spreads across two.
    assert!(
        out.contains("rewrite [2] in FR : (a | a) | a .\nrewrites: 2\nresult S: (a | a) | c"),
        "greedy:\n{out}"
    );
    assert!(out.contains("frewrite [2] in FR : (a | a) | a .\nrewrites: 2\nresult (sort not calculated): (b | b) | a"), "fair + sort-not-calculated:\n{out}");
    // Frozen: a rule never rewrites inside f's (frozen) argument; g's argument IS rewritten.
    assert!(
        out.contains("frewrite in FR : f(a) .\nrewrites: 0\nresult S: f(a)"),
        "frozen blocks:\n{out}"
    );
    assert!(
        out.contains("frewrite in FR : g(a) .\nrewrites: 3\nresult S: g(d)"),
        "non-frozen rewrites:\n{out}"
    );
}

/// Conditional rules backtrack across equality, matching, and sort-test fragments.
#[test]
fn crl_command_through_repl() {
    let out = repl().eval(conformance_file!("crl.maude")).output;
    assert!(
        out.contains("rewrite in CRL : f(a) .\nrewrites: 1\nresult S: g(a)"),
        "equality holds:\n{out}"
    );
    assert!(
        out.contains("rewrite in CRL : f(b) .\nrewrites: 1\nresult S: h(b)"),
        "backtrack to `:=`:\n{out}"
    );
    assert!(
        out.contains("rewrite in CRL : k(a) .\nrewrites: 1\nresult S: g(a)"),
        "sort-test holds:\n{out}"
    );
    assert!(
        out.contains("rewrite in CRL : k(b) .\nrewrites: 0\nresult S: k(b)"),
        "sort-test fails -> no rewrite:\n{out}"
    );
}

/// A traced `crl` renders its rule trial, condition fragments, and backtracking: trial #1 fails its
/// `X = a` fragment, then trial #2 binds `Y := X` and fires the rule.
#[test]
fn traced_crl_backtrack() {
    let s = run_session(
        "mod CRL is sort S . ops a b : -> S . ops f g h : S -> S [ctor] . vars X Y : S . \
         crl f(X) => g(X) if X = a . crl f(X) => h(Y) if Y := X . endm\n\
         set trace on .\n\
         rewrite f(b) .",
    );
    assert!(
        s.contains("*********** trial #1\ncrl f(X) => g(X) if X = a .\nX --> b"),
        "trial #1:\n{s}"
    );
    assert!(
        s.contains("*********** failure for condition fragment\nX = a"),
        "fragment failure:\n{s}"
    );
    assert!(s.contains("*********** failure #1"), "trial #1 fails:\n{s}");
    assert!(
        s.contains("*********** trial #2\ncrl f(X) => h(Y) if Y := X ."),
        "trial #2:\n{s}"
    );
    assert!(
        s.contains("*********** success #2"),
        "trial #2 succeeds:\n{s}"
    );
    assert!(
        s.contains(
            "*********** rule\ncrl f(X) => h(Y) if Y := X .\nX --> b\nY --> b\nf(b)\n--->\nh(b)"
        ),
        "rule fires:\n{s}"
    );
}

/// Search covers all four arrows, shared states, `such that`, bounded enumeration, and `continue`.
#[test]
fn search_command_through_repl() {
    let out = repl().eval(conformance_file!("search.maude")).output;
    // =>1: exactly the one-step successors b, c (states 3, rewrites 2 at the end).
    assert!(
        out.contains(
            "search in NDET : a =>1 X .\n\nSolution 1 (state 1)\nstates: 2  rewrites: 1\nX --> b"
        ),
        "=>1 sol1:\n{out}"
    );
    assert!(out.contains("Solution 2 (state 2)\nstates: 3  rewrites: 2\nX --> c\n\nNo more solutions.\nstates: 3  rewrites: 2"), "=>1 sol2+end:\n{out}");
    // =>* includes the initial state 0 at rewrites 0.
    assert!(
        out.contains(
            "search in NDET : a =>* X .\n\nSolution 1 (state 0)\nstates: 1  rewrites: 0\nX --> a"
        ),
        "=>* state 0:\n{out}"
    );
    // =>! finds only the normal form e (whole graph explored: states 5, rewrites 5).
    assert!(out.contains("search in NDET : a =>! X .\n\nSolution 1 (state 4)\nstates: 5  rewrites: 5\nX --> e\n\nNo more solutions."), "=>! e:\n{out}");
    // such that filters to state 3 (d), but exploration still finishes the whole graph.
    assert!(out.contains("such that X = d .\n\nSolution 1 (state 3)\nstates: 4  rewrites: 3\nX --> d\n\nNo more solutions.\nstates: 5  rewrites: 5"), "such-that:\n{out}");
    // [1] then continue: the second solution c is generated lazily during continue, so rewrites: 1.
    assert!(out.contains("search [1] in NDET : a =>+ X .\n\nSolution 1 (state 1)\nstates: 2  rewrites: 1\nX --> b\n\nSolution 2 (state 2)\nstates: 3  rewrites: 1\nX --> c"), "bounded+continue:\n{out}");
}

/// `show path N` and `show search graph` render transition history and the reachable-state graph.
#[test]
fn search_show_path_and_graph() {
    let s = run_session(
        "mod NDET is sort St . ops a b c d e : -> St . var X : St . \
         rl a => b . rl a => c . rl b => d . rl c => d . rl d => e . endm\n\
         search a =>! X .\n\
         show path 4 .\n\
         show search graph .",
    );
    assert!(
        s.contains("state 0, St: a\n===[ rl a => b . ]===>\nstate 1, St: b\n===[ rl b => d . ]===>\nstate 3, St: d\n===[ rl d => e . ]===>\nstate 4, St: e"),
        "show path:\n{s}"
    );
    assert!(
        s.contains(
            "state 0, St: a\narc 0 ===> state 1 (rl a => b .)\narc 1 ===> state 2 (rl a => c .)"
        ),
        "show graph state 0:\n{s}"
    );
    assert!(
        s.contains("state 3, St: d\narc 0 ===> state 4 (rl d => e .)"),
        "show graph state 3:\n{s}"
    );
}

/// Rewrite-condition fragments perform nested reachability search, including zero-step matches and fresh bindings.
#[test]
fn rewrite_condition_through_repl() {
    let out = repl().eval(conformance_file!("rewrite-cond.maude")).output;
    // X => c holds via a->b->c (2 search rewrites) + the rule itself = 3.
    assert!(
        out.contains("rewrite in REACH : f(a) .\nrewrites: 3\nresult S: done"),
        "reach a:\n{out}"
    );
    // c matches c at 0 steps -> just the rule fires (1 rewrite).
    assert!(
        out.contains("rewrite in REACH : f(c) .\nrewrites: 1\nresult S: done"),
        "reach c (0 steps):\n{out}"
    );
    // stuck reaches nothing matching c -> condition fails, no rewrite.
    assert!(
        out.contains("rewrite in REACH : f(stuck) .\nrewrites: 0\nresult S: f(stuck)"),
        "unreachable:\n{out}"
    );
    // The target `s(Y)` binds `Y` from the reached state; the chosen `=>` path yields `Y = z` after two
    // rewrites.
    assert!(
        out.contains("rewrite in BIND : f(s(s(z))) .\nrewrites: 2\nresult N: g(z)"),
        "binding:\n{out}"
    );
}

/// A rewrite condition (`=>`) is legal only in a rule. An equation using one is dropped with an
/// actionable warning, while the module and its following commands remain usable.
#[test]
fn rewrite_condition_dropped_in_equation() {
    let mut r = repl();
    let warning = r
        .eval(
            "fmod E is\n\
               sort S .\n\
               ops a b : -> S .\n\
               var X : S .\n\
               ceq a = b if X => b .\n\
             endfm",
        )
        .output;
    assert_eq!(
        warning,
        wrap::auto_wrap(
            "warning: module `E`, line 5: dropped equation: a rewrite condition (`=>`) is only \
             allowed in a rule (`crl`), not an equation"
        )
    );

    let output = r.eval("reduce in E : a .").output;
    assert!(
        output.contains("rewrites: 0\nresult S: a"),
        "module usable, bad ceq dropped: {output}"
    );
    assert!(
        !output.contains("result S: b"),
        "the dropped ceq must not fire: {output}"
    );
}

/// On-the-fly colon variables `X:Sort` (one token) parse anywhere a term is expected — in an `eq`
/// (mixed with declared vars), a `match` pattern, and a `search` goal — without a `var` declaration. A
/// variable with no declared spelling is echoed back with its sort.
#[test]
fn on_the_fly_colon_variables() {
    let mut r = repl();
    r.eval(
        "fmod N is sort Nat . op z : -> Nat . op s_ : Nat -> Nat [ctor] . op _+_ : Nat Nat -> Nat . \
         op dbl : Nat -> Nat . vars M N : Nat . eq N + z = N . eq N + s M = s (N + M) . \
         eq dbl(N:Nat) = N:Nat + N:Nat . endfm",
    );
    assert!(
        r.eval("red dbl(s s z) .")
            .output
            .contains("result Nat: s s s s z"),
        "on-the-fly var in an eq"
    );
    assert!(
        r.eval("match X:Nat <=? s z .")
            .output
            .contains("X:Nat --> s z"),
        "on-the-fly var in match, with sort"
    );
    // …and in a system module's search goal.
    r.eval("mod S is sort T . ops p q : -> T . rl p => q . endm");
    let s = r.eval("search p =>1 Y:T .").output;
    assert!(
        s.contains("Y:T --> q"),
        "on-the-fly var in a search goal:\n{s}"
    );
}

/// A variable is identified by its base name and resolved sort, so within one statement or command the
/// declared `X : Q` and the on-the-fly `X:Q` are one variable, as are the kind spellings `X:[P]` and
/// `X:[Q]`. The equation is kept, matching demands one value, and each unifier is sound.
#[test]
fn declared_and_colon_spellings_are_one_variable() {
    let mut r = repl();
    let load = r.eval(
        "fmod VARID is sorts P Q R . subsorts P < Q R . ops p p2 : -> P . \
         op f : [Q] [Q] -> [Q] . op g : Q -> Q . var X : Q . eq g(X) = X:Q . endfm",
    );
    assert!(!load.output.contains("dropped"), "{}", load.output);
    let red = r.eval("red g(p) .").output;
    assert!(
        red.contains("rewrites: 1") && red.contains("result P: p"),
        "{red}"
    );
    let matched = r.eval("match f(X, X:Q) <=? f(p, p2) .").output;
    assert!(matched.contains("No match."), "{matched}");
    let matched = r.eval("match f(X, X:Q) <=? f(p, p) .").output;
    assert!(
        matched.trim_end().ends_with("Matcher 1\nX --> p"),
        "{matched}"
    );
    let unified = r.eval("unify f(X, p) =? f(X:Q, p) /\\ X:Q =? p .").output;
    assert!(
        unified.trim_end().ends_with("Unifier 1\nX --> p"),
        "{unified}"
    );
    let unified = r
        .eval("unify f(X:[P], p) =? f(X:[Q], p) /\\ X:[Q] =? p2 .")
        .output;
    assert!(
        unified.trim_end().ends_with("Unifier 1\nX:[P] --> p2"),
        "{unified}"
    );
}

/// A search condition may name the goal variable by its other spelling; the condition is then bound by
/// the goal rather than reaching instantiation unbound.
#[test]
fn search_condition_may_use_another_spelling_of_a_goal_variable() {
    let mut r = repl();
    r.eval(
        "mod VSC is sorts P Q . subsort P < Q . ops p p2 : -> P . op c : Q -> Q . var X : Q . \
         rl c(X) => X . endm",
    );
    let out = r.eval("search c(p) =>1 X:Q such that X = p .").output;
    assert!(
        out.contains("Solution 1 (state 1)") && out.contains("X:Q --> p"),
        "{out}"
    );
    let out = r.eval("search c(p2) =>1 X such that X:Q = p .").output;
    assert!(
        out.contains("No more solutions.") && !out.contains("Solution 1"),
        "{out}"
    );
}

/// A matchrew `by` variable may be written in any spelling of a pattern variable.
#[test]
fn matchrew_by_resolves_any_spelling_of_a_pattern_variable() {
    let mut r = repl();
    r.eval(
        "mod VMR is sorts P Q . subsort P < Q . ops p p2 : -> P . op f : Q Q -> Q . var X : Q . \
         rl [two] : p => p2 . endm",
    );
    let both = r
        .eval("srew f(p, p) using matchrew f(X, X:Q) by X:Q using two .")
        .output;
    assert!(both.contains("result Q: f(p2, p2)"), "{both}");
    let declared = r
        .eval("srew f(p, p) using matchrew f(X, Y:Q) by X:Q using two .")
        .output;
    assert!(declared.contains("result Q: f(p2, p)"), "{declared}");
    let absent = r
        .eval("srew f(p, p) using matchrew f(X, Y:Q) by Z:Q using two .")
        .output;
    assert!(
        absent.contains("matchrew variable `Z:Q` does not occur in the pattern"),
        "{absent}"
    );
}

/// Object completion's fresh class variable for `Account` must not be the written `V:Account`, which is
/// the variable `V` of sort `Account`: the two objects may belong to different subclasses.
#[test]
fn object_completion_fresh_variable_avoids_written_spelling() {
    let mut r = repl();
    let load = r.eval(
        "omod SWAP is
  sort Val .
  ops v1 v2 : -> Val [ctor] .
  class Account | bal : Val .
  class Savings | rate : Val .
  subclass Savings < Account .
  ops a b : -> Oid [ctor] .
  msg swap : Oid Oid -> Msg .
  vars A B : Oid .
  vars N M : Val .
  rl [swap] : swap(A, B) < A : V:Account | bal : N > < B : Account | bal : M >
    => < A : V:Account | bal : M > < B : Account | bal : N > .
endom",
    );
    assert!(!load.output.contains("error"), "{}", load.output);
    let out = r
        .eval(
            "rewrite swap(b, a) < a : Savings | bal : v1, rate : v1 > < b : Account | bal : v2 > .",
        )
        .output;
    assert!(
        out.contains("rewrites: 1") && out.contains("< a : Savings | bal : v2, rate : v1 >"),
        "{out}"
    );
}

/// A rule in a functional module (`fmod`) is rejected — rules belong only to system modules (`mod`).
#[test]
fn rule_in_fmod_is_rejected() {
    let out = repl()
        .eval("fmod F is sort S . ops a b : -> S . rl a => b . endfm")
        .output;
    assert_eq!(
        out,
        wrap::auto_wrap(
            "parse error: module `F`, line 1: rule `rl` is not allowed in a functional module \
             (`fmod F`); use `mod`"
        )
    );
}

/// A single `eval` handles a file containing a module, a `set trace on .` meta-command, and a traced
/// command. Statement dispatch preserves REPL state across `show`, `continue`, and related commands.
#[test]
fn eval_mixed_file_with_meta_commands() {
    let out = repl()
        .eval(
            "mod CH is sort S . ops a b c : -> S . rl a => b . rl b => c . endm\n\
             set trace on .\n\
             rewrite a .",
        )
        .output;
    assert!(
        out.contains("*********** rule\nrl a => b ."),
        "traced rule from a one-shot file load:\n{out}"
    );
    assert!(out.contains("rewrites: 2\nresult S: c"), "result:\n{out}");
}

/// The multi-line buffer boundary: a command terminator / a closed module complete; an open module body
/// or a terminator-less line keep buffering; a bare `quit` completes.
#[test]
fn input_complete_boundaries() {
    let mut r = repl();
    assert!(r.input_complete("red x ."), "command terminator");
    assert!(
        r.input_complete("fmod M is sort S . endfm"),
        "closed module"
    );
    assert!(
        !r.input_complete("fmod M is sort S ."),
        "open module body keeps buffering"
    );
    assert!(!r.input_complete("red x"), "no terminator");
    assert!(r.input_complete("quit"), "bare quit");
    assert!(r.input_complete("q"), "bare q");
    assert!(!r.input_complete(""), "empty");
    assert!(!r.input_complete("   \n  "), "whitespace");
}

/// Extract non-echo outcome lines from an object-system run. Command echoes, including wrapped
/// continuations through the trailing ` .`, are removed; result, rewrite/state count, solution, and
/// binding lines remain for assertions.
fn objects_outcomes(out: &str) -> Vec<String> {
    let mut lines = out.lines().peekable();
    let mut keep = Vec::new();
    while let Some(line) = lines.next() {
        if matches!(
            line.split(' ').next(),
            Some("rewrite" | "reduce" | "search" | "erewrite")
        ) {
            // Skip the echo block: this line plus continuations, through the trailing ` .`.
            let mut l = line;
            while !l.trim_end().ends_with('.') {
                match lines.next() {
                    Some(next) => l = next,
                    None => break,
                }
            }
            continue;
        }
        keep.push(line.to_string());
    }
    keep
}

/// Exercise object-message configurations under ordinary rewrite and search, including configuration
/// hooks, class lookup, and arity-first canonical ordering of messages and objects.
#[test]
fn objects_through_repl() {
    let out = repl().eval(conformance_file!("objects.maude")).output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "objects build: {out}"
    );
    assert!(!out.contains("parse error"), "no parse errors: {out}");
    assert_eq!(
        objects_outcomes(&out),
        vec![
            // BANK: two credits apply (4 rewrites), balances updated, objects in `a < b` order.
            "rewrites: 4",
            "result Configuration: < a : Account | bal : 50 > < b : Account | bal : 125 >",
            // getClass: an ordinary equation over the object constructor.
            "rewrites: 1",
            "result Cid: Account",
            // BANK search: credit 5 then 7 reaches balance 12 (state 3 of 4); declared var `N` prints bare.
            "",
            "Solution 1 (state 3)",
            "states: 4  rewrites: 6",
            "N --> 12",
            "",
            "No more solutions.",
            "states: 4  rewrites: 8",
            // PINGPONG `rewrite [4]`: four message hand-offs; the leftover `ping(p1, p2)` (arity 2) prints
            // BEFORE the two arity-3 objects — the arity-first ACU order. (Result wraps at 80 cols.)
            "rewrites: 4",
            "result Configuration: ping(p1, p2) < p1 : Player | turns : 2 > < p2 : Player |",
            "    turns : 2 >",
            // PINGPONG search `=>+`: the first `pong(p2, p1)` state (depth 1), the soup remainder bound to C.
            "",
            "Solution 1 (state 1)",
            "states: 2  rewrites: 1",
            "C:Configuration --> < p1 : Player | turns : 1 > < p2 : Player | turns : 0 >",
            // `erewrite` uses the object-message scheduler. Both credits are delivered in one pass.
            "rewrites: 4",
            "result Configuration: < a : Account | bal : 50 > < b : Account | bal : 125 >",
            // BANK, two credits to ONE account: `a` evolves 0->5->12 within the pass; the lone object
            // collapses to `result Object:`.
            "rewrites: 4",
            "result Object: < a : Account | bal : 12 >",
            // PINGPONG `erewrite [3]`: one delivery per pass (each produces the next message), so [3] = 3
            // hand-offs — pong leftover, p1 at 2 turns, p2 at 1. (Result wraps at 80 cols.)
            "rewrites: 3",
            "result Configuration: pong(p2, p1) < p1 : Player | turns : 2 > < p2 : Player |",
            "    turns : 1 >",
        ],
        "object outcomes (echoes/rate aside): {out}"
    );
}

/// External `erewrite` processes standard-stream messages synchronously and emits side-channel output in
/// request/reply order.
#[test]
fn objects_io_through_repl() {
    let mut r = repl();
    r.set_stdin("one\ntwo\n"); // piped stdin for ECHO's getLine
    let out = r.eval(conformance_file!("objects-io.maude")).output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "io build: {out}"
    );
    assert!(!out.contains("parse error"), "no parse errors: {out}");
    assert_eq!(
        objects_outcomes(&out),
        vec![
            // GREET: start -> write "hello\n" -> wrote -> stop. The write happens externally (not a
            // rewrite); the count is the `go`+`done` rules = 2.
            "hello",
            "rewrites: 2",
            "result Configuration: <> < g : Greeter | none >",
            // TICKER: three sequential "tick\n" writes (go + next + next), then stop = 4 rule rewrites.
            "tick",
            "tick",
            "tick",
            "rewrites: 4",
            "result Configuration: <> < t : Ticker | n : 0 >",
            // ECHO: getLine reads "one\n"/"two\n" (incl. newline), each echoed straight to stdout; count is
            // go + got + next + got + stop = 5 rule rewrites (the getLine/write handling is not a rewrite).
            "one",
            "two",
            "rewrites: 5",
            "result Configuration: <> < e : Echoer | n : 0 >",
        ],
        "STD-STREAM stdout writes + stdin getLine + erewrite outcomes: {out}"
    );
}

#[test]
fn erewrite_parse_failure_preserves_pending_stdin() {
    let mut r = repl();
    let (modules, _) = conformance_file!("objects-io.maude")
        .split_once("erewrite in GREET")
        .expect("objects-io command boundary");
    let loaded = r.eval(modules);
    assert!(
        !loaded.exit && !loaded.output.contains("error in module"),
        "{}",
        loaded.output
    );

    r.set_stdin("kept\n");
    let rejected = r.eval("erewrite in ECHO : bogus .");
    assert!(
        rejected
            .output
            .contains("error: no parse at token 0 (`bogus`)"),
        "{}",
        rejected.output
    );

    let recovered = r.eval("erewrite in ECHO : <> start(e) < e : Echoer | n : (s 0) > .");
    assert!(
        recovered.output.contains("\nkept\n"),
        "failed erewrite must not consume pending stdin: {}",
        recovered.output
    );
}

/// Object-oriented modules desugar classes, subclasses, attributes, and messages into CONFIGURATION.
/// Pattern completion preserves unmatched attributes and permits superclass rules to match subclass objects.
#[test]
fn objects_omod_through_repl() {
    let out = repl().eval(conformance_file!("objects-omod.maude")).output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "omod build: {out}"
    );
    assert!(!out.contains("parse error"), "no parse errors: {out}");
    assert_eq!(
        objects_outcomes(&out),
        vec![
            // rewrite: credit fires on the Account and on the Savings subclass (its extra `rate` preserved).
            "rewrites: 4",
            "result Configuration: < a : Account | bal : 50 > < b : Savings | bal : 125,",
            "    rate : 5 >",
            // getClass on the subclass instance returns its actual class.
            "rewrites: 1",
            "result Savings: Savings",
            // search: credit 5 then 7 reaches balance 12 (state 3 of 4).
            "",
            "Solution 1 (state 3)",
            "states: 4  rewrites: 6",
            "N --> 12",
            "",
            "No more solutions.",
            "states: 4  rewrites: 8",
            // erewrite (object-message-fair): one pass delivers both credits.
            "rewrites: 4",
            "result Configuration: < a : Account | bal : 50 > < b : Savings | bal : 125,",
            "    rate : 5 >",
            // erewrite ping-pong: [3] = three hand-offs; pong leftover, p1 at 2 turns, p2 at 1.
            "rewrites: 3",
            "result Configuration: pong(p2, p1) < p1 : Player | turns : 2 > < p2 : Player |",
            "    turns : 1 >",
        ],
        "omod/class/subclass/msg + object-pattern completion outcomes: {out}"
    );
}

/// Object-pattern completion preserves RHS-omitted attributes and constrains RHS-added attributes to objects
/// that already carry them.
#[test]
fn objects_omod_attrs_through_repl() {
    let out = repl()
        .eval(conformance_file!("objects-omod-attrs.maude"))
        .output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "omod-attrs build: {out}"
    );
    assert!(!out.contains("parse error"), "no parse errors: {out}");
    assert_eq!(
        objects_outcomes(&out),
        vec![
            // applyRate: bal := bal + rate (100 + 5); rate preserved via the missing-attribute copy.
            "rewrites: 2",
            "result Object: < s1 : Savings | bal : 105, rate : 5 >",
            // log: count := s count, last := 7 (last matched by a fresh kind-variable on the LHS).
            "rewrites: 1",
            "result Object: < lg : Logger | count : 1, last : 7 >",
        ],
        "object-pattern completion attribute edge cases: {out}"
    );
}

/// The object-message scheduler handles both its single-object fast path and generic multi-object path.
#[test]
fn objects_omod_multi_through_repl() {
    let out = repl()
        .eval(conformance_file!("objects-omod-multi.maude"))
        .output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "multi build: {out}"
    );
    assert!(!out.contains("parse error"), "no parse errors: {out}");
    assert_eq!(
        objects_outcomes(&out),
        vec![
            // reward(a,5) via the fast path (a: 0->5, +1 for the `+`), then pair via leftOver (a->6, b->1) = 3.
            "rewrites: 3",
            "result Configuration: < a : Member | pts : 6 > < b : Member | pts : 1 >",
            // pair alone: one leftOver rewrite bumps both objects.
            "rewrites: 1",
            "result Configuration: < a : Member | pts : 1 > < b : Member | pts : 1 >",
        ],
        "erewrite object-message fast path + multi-object leftOver path: {out}"
    );
}

/// Object theories share object-module desugaring and return the concrete class of subclass instances.
#[test]
fn objects_oth_through_repl() {
    let out = repl().eval(conformance_file!("objects-oth.maude")).output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "oth build: {out}"
    );
    assert!(!out.contains("parse error"), "no parse errors: {out}");
    assert_eq!(
        objects_outcomes(&out),
        vec![
            "rewrites: 1",
            "result Shape: Shape",
            // getClass on a Square (a subclass of Shape) instance returns its own class.
            "rewrites: 1",
            "result Square: Square",
        ],
        "oth (object theory) class/subclass/msg build + getClass: {out}"
    );
}

/// Object modules round-trip through `upModule` and `metaRewrite`, preserving completed patterns and spaced
/// mixfix attribute names.
#[test]
fn objects_omod_meta_through_repl() {
    let mut r = repl();
    r.eval(conformance_file!("prelude-meta.maude")); // load the META-LEVEL tower
    let out = r
        .eval(concat!(
            "omod BANK is\n",
            "  protecting NAT .\n",
            "  class Account | bal : Nat .\n",
            "  ops a b : -> Oid [ctor] .\n",
            "  msg credit : Oid Nat -> Msg .\n",
            "  vars A : Oid .  vars N M : Nat .\n",
            "  rl [credit] : credit(A, M) < A : Account | bal : N > => < A : Account | bal : (N + M) > .\n",
            "endom\n",
            "red in META-LEVEL : upModule('BANK, false) .\n",
            "red in META-LEVEL : metaRewrite(upModule('BANK, false), ",
            "'__['credit['a.Oid, 's_^5['0.Zero]], ",
            "'<_:_|_>['a.Oid, 'Account.Account, 'bal`:_['0.Zero]]], unbounded) .\n",
        ))
        .output;
    assert!(
        !out.contains("no parse") && !out.contains("error"),
        "omod meta: {out}"
    );
    // upModule: the message op is `[ctor msg]`, the attribute op is spelled with the backtick-blank.
    assert!(
        out.contains("op 'credit : 'Oid 'Nat -> 'Msg [ctor msg] ."),
        "upModule [ctor msg]: {out}"
    );
    assert!(
        out.contains("op 'bal`:_ : 'Nat -> 'Attribute [ctor gather('&)] ."),
        "attr op name: {out}"
    );
    // metaRewrite: credit delivered, balance 0 -> 5, attribute op spelled `` 'bal`:_ `` in the result.
    assert!(
        out.contains("'bal`:_['s_^5["),
        "metaRewrite result must spell the attribute op with the backtick-blank and reduce the balance: {out}"
    );
}

/// Object theories up-translate completed rules with class variables, residual attributes, and exact
/// attribute-operator spelling.
#[test]
fn objects_oth_meta_through_repl() {
    let mut r = repl();
    r.eval(conformance_file!("prelude-meta.maude"));
    let out = r
        .eval(concat!(
            "oth OT is\n",
            "  protecting NAT .\n",
            "  class Acct | bal : Nat .\n",
            "  op c : -> Oid [ctor] .\n",
            "  msg cr : Oid Nat -> Msg .\n",
            "  vars A : Oid .  vars N M : Nat .\n",
            "  rl [cr] : cr(A, M) < A : Acct | bal : N > => < A : Acct | bal : (N + M) > .\n",
            "endoth\n",
            "red in META-LEVEL : upModule('OT, false) .\n",
        ))
        .output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "oth meta: {out}"
    );
    // The oth up-translates to a `th` (theory), and its rule is completed and shown.
    assert!(
        out.contains("th 'OT is"),
        "oth up-translates to a theory: {out}"
    );
    // The rule is object-pattern-completed: class constant -> fresh `'V:Acct`, a fresh attribute-set
    // variable `'Atts:AttributeSet`, and the attribute op spelled with the backtick-blank. (The full rule
    // wraps at 80 columns, so assert the individual completion markers.)
    for marker in ["'V:Acct", "'Atts:AttributeSet", "'bal`:_[", "[label('cr)]"] {
        assert!(
            out.contains(marker),
            "oth rule missing completion marker `{marker}`: {out}"
        );
    }
}

/// `upEqs`/`upMbs`/`upRls` retain a module's own `[nonexec]` axioms and labels in declaration order.
/// Non-executable statements have no engine traces, so up-translation parses their stored bubbles on
/// demand. Executable equation labels are retained as well.
#[test]
fn meta_nonexec_up_through_repl() {
    let mut r = repl();
    r.eval(conformance_file!("prelude-meta.maude"));
    let out = r
        .eval(concat!(
            // Declare the executable equation first to exercise declaration-order retention.
            "fth ORDA is\n",
            "  sorts Elt .\n",
            "  op a : -> Elt [ctor] .\n",
            "  op f : Elt -> Elt .  op g : Elt -> Elt .\n",
            "  var X : Elt .\n",
            "  eq f(X) = X .\n",
            "  eq g(X) = X [nonexec label gx] .\n",
            "endfth\n",
            // Executable equation labels are retained.
            "fmod LBL is\n",
            "  sorts S .  op a : -> S [ctor] .  op f : S -> S .  var X : S .\n",
            "  eq f(X) = X [label fx] .\n",
            "endfm\n",
            // nonexec memberships: plain + conditional.
            "fth MBX is\n",
            "  sorts S T .  subsort T < S .  op a : -> S [ctor] .  op p : S -> S .  var X : S .\n",
            "  mb a : T [nonexec label mbax] .\n",
            "  cmb p(X) : T if X : T [nonexec label cmbax] .\n",
            "endfth\n",
            // A non-executable labelled rule followed by an executable rule.
            "mod RLX is\n",
            "  sorts S .  ops a b : -> S [ctor] .  op f : S -> S .  var X : S .\n",
            "  rl [rax] : f(X) => X [nonexec] .\n",
            "  rl f(a) => b .\n",
            "endm\n",
            "red in META-LEVEL : upEqs('ORDA, false) .\n",
            "red in META-LEVEL : upEqs('ORDA, true) .\n", // Exercises the flat merge with no imports.
            "red in META-LEVEL : upEqs('LBL, false) .\n",
            "red in META-LEVEL : upMbs('MBX, false) .\n",
            "red in META-LEVEL : upRls('RLX, false) .\n",
        ))
        .output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "nonexec up: {out}"
    );
    // The nonexec eq is retained with `[nonexec label('gx)]`, in declaration order after the exec `[none]`.
    assert!(
        out.contains(
            "eq 'f['X:Elt] = 'X:Elt [none] .\neq 'g['X:Elt] = 'X:Elt [nonexec label('gx)] ."
        ),
        "nonexec eq retained in declaration order: {out}"
    );
    // An executable equation's own `[label]` is retained.
    assert!(
        out.contains("eq 'f['X:S] = 'X:S [label('fx)] ."),
        "executable eq label: {out}"
    );
    // Nonexec memberships (plain + conditional) retained with their labels.
    assert!(
        out.contains("mb 'a.S : 'T [nonexec label('mbax)] ."),
        "nonexec mb: {out}"
    );
    assert!(
        out.contains("cmb 'p['X:S] : 'T if 'X:S : 'T [nonexec label('cmbax)] ."),
        "nonexec cmb: {out}"
    );
    // Nonexec rule retained (with its label), then the executable rule as `[none]`, in declaration order.
    assert!(
        out.contains("rl 'f['X:S] => 'X:S [nonexec label('rax)] .\nrl 'f['a.S] => 'b.S [none] ."),
        "nonexec rule retained in declaration order: {out}"
    );
}

/// Multi-token operator names preserve load-bearing inter-token blanks as backquotes in their canonical
/// spelling. `op c d_` remains distinct from `op cd_`; space and backquote spellings tokenize to the same
/// name, and escaped special names remain unaffected. These operators lex, parse, reduce, and print
/// through the REPL.
#[test]
fn multitoken_op_through_repl() {
    let out = repl().eval(conformance_file!("multitoken-op.maude")).output;
    assert!(
        !out.contains("no parse") && !out.contains("error"),
        "multitoken op: {out}"
    );
    assert!(out.contains("result S: a b"), "2-token constant: {out}");
    assert!(
        out.contains("result S: c d a b"),
        "mixfix over a 2-token arg: {out}"
    );
    assert!(
        out.contains("result S: a b e f a b"),
        "infix with multiple literals: {out}"
    );
    assert!(
        out.contains("result S: done[done]"),
        "escaped-bracket op still works: {out}"
    );
    // `g(a b) = done` fires over a multi-token subterm, via BOTH the space and backquote forms.
    assert_eq!(
        out.matches("result S: done\n").count(),
        2,
        "the equation fires for both `g(a b)` and `g(a`b)`: {out}"
    );
}

/// META round-trips preserve multi-token operator names. `upModule` encodes inter-token blanks as
/// backquotes, and `metaReduce` resolves and reduces hand-written meta terms that use those Qids.
#[test]
fn multitoken_op_meta_through_repl() {
    let mut r = repl();
    r.eval(conformance_file!("prelude-meta.maude")); // Defines `upModule` and `metaReduce`.
    let out = r
        .eval(concat!(
            "fmod MT is\n",
            "  sorts S .\n",
            "  op a b : -> S [ctor] .\n",
            "  op c d_ : S -> S .\n",
            "  op z : -> S [ctor] .\n",
            "  eq c d (a b) = z .\n",
            "endfm\n",
            "red in META-LEVEL : upModule('MT, false) .\n",
            "red in META-LEVEL : metaReduce(upModule('MT, false), 'c`d_['a`b.S]) .\n",
        ))
        .output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "multitoken meta: {out}"
    );
    // upModule spells the blank as a backquote in each op's name.
    assert!(
        out.contains("op 'a`b : nil -> 'S [ctor] ."),
        "up: 2-token constant name: {out}"
    );
    assert!(
        out.contains("op 'c`d_ : 'S -> 'S [none] ."),
        "up: mixfix name: {out}"
    );
    // metaReduce down-translates the backquote Qid and reduces `c d (a b)` to `z`.
    assert!(
        out.contains("result ResultPair: {'z.S, 'S}"),
        "down: metaReduce over a backquote Qid: {out}"
    );
}

/// A signature-owned compound identity survives a complete metalevel module round-trip. `upModule` emits
/// the identity as a structural meta-term; feeding that module to `metaReduce` resolves its target symbols
/// and collapses the identity during construction.
#[test]
fn compound_identity_meta_roundtrip_through_repl() {
    let mut r = repl();
    r.eval(conformance_file!("prelude-meta.maude"));
    let out = r
        .eval(concat!(
            "fmod ID-META is\n",
            "  sort S .\n",
            "  ops a b : -> S [ctor] .\n",
            "  op pair : S S -> S [ctor] .\n",
            "  op join : S S -> S [assoc id: pair(a,b)] .\n",
            "endfm\n",
            "red in META-LEVEL : upModule('ID-META, false) .\n",
            "red in META-LEVEL : metaReduce(upModule('ID-META, false), ",
            "'join['pair['a.S, 'b.S], 'a.S]) .\n",
        ))
        .output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "compound id meta: {out}"
    );
    assert!(
        out.contains("op 'join : 'S 'S -> 'S [assoc id('pair['a.S, 'b.S])] ."),
        "upModule structural identity: {out}"
    );
    assert!(
        out.contains("rewrites: 2") && out.contains("result ResultPair: {'a.S, 'S}"),
        "down-translated identity collapse: {out}"
    );
}

/// Down-module identity leaves retain their meta-term sort qualification rather than collapsing to a
/// constant spelling. The two `a` declarations share one connected component, so `(a).S` is load-bearing
/// when `upModule` is rebuilt as the target signature.
#[test]
fn overloaded_constant_identity_meta_roundtrip_through_repl() {
    let mut r = repl();
    r.eval(conformance_file!("prelude-meta.maude"));
    let out = r
        .eval(concat!(
            "fmod ID-META-OVERLOAD is\n",
            "  sorts S U . subsort U < S .\n",
            "  op a : -> S [ctor] .\n",
            "  op a : -> U [ctor] .\n",
            "  op b : -> S [ctor] .\n",
            "  op pair : S S -> S [ctor] .\n",
            "  op join : S S -> S [assoc id: pair((a).S,b)] .\n",
            "endfm\n",
            "red in META-LEVEL : metaReduce(upModule('ID-META-OVERLOAD, false), ",
            "'join['pair['a.S, 'b.S], 'b.S]) .\n",
        ))
        .output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "qualified id meta: {out}"
    );
    assert!(
        out.contains("rewrites: 2") && out.contains("result ResultPair: {'b.S, 'S}"),
        "qualified overload identity collapse: {out}"
    );
}

/// The same metalevel identity path stays compact for an iterated million-count subterm: neither
/// `upModule` nor rebuilding its `id(...)` expands the static term into a recursive unary chain.
#[test]
fn compact_iter_identity_meta_roundtrip_through_repl() {
    let mut r = repl();
    r.eval(conformance_file!("prelude-meta.maude"));
    let out = r
        .eval(concat!(
            "fmod ID-META-ITER is\n",
            "  sort S .\n",
            "  op a : -> S [ctor] .\n",
            "  op g : S -> S [ctor iter] .\n",
            "  op f : S -> S .\n",
            "  op join : S S -> S [assoc id: g^1000000(a)] .\n",
            "  eq f(g^1000000(a)) = a .\n",
            "endfm\n",
            "red in META-LEVEL : upModule('ID-META-ITER, false) .\n",
            "red in META-LEVEL : metaReduce(upModule('ID-META-ITER, false), ",
            "'join['g^1000000['a.S], 'a.S]) .\n",
            "red in META-LEVEL : metaReduce(upModule('ID-META-ITER, false), ",
            "'f['g^1000000['a.S]]) .\n",
        ))
        .output;
    assert!(
        !out.contains("no parse") && !out.contains("error in module"),
        "compact id meta: {out}"
    );
    assert!(
        out.contains("id('g^1000000['a.S])"),
        "upModule preserves the compact compound identity: {out}"
    );
    assert!(
        out.contains("rewrites: 2") && out.contains("result ResultPair: {'a.S, 'S}"),
        "down-translated compact identity collapse: {out}"
    );
    assert!(
        out.contains("rewrites: 3"),
        "inline equation's compact static Term::Iter down/up path: {out}"
    );
}

fn variant_sequence_lines(output: &str) -> Vec<String> {
    output
        .lines()
        .filter_map(|line| {
            if let Some(rest) = line.strip_prefix("rewrites: ") {
                return Some(format!(
                    "rewrites: {}",
                    rest.split_whitespace().next().unwrap_or("?")
                ));
            }
            [
                "get variants",
                "variant unify",
                "variant match",
                "Variant ",
                "Unifier ",
                "Matcher ",
                "S:",
                "X -->",
                "Y -->",
                "Z -->",
                "No more ",
            ]
            .iter()
            .any(|prefix| line.starts_with(prefix))
            .then(|| line.to_string())
        })
        .collect()
}

fn one_rewrite_count(output: &str) -> u64 {
    output
        .lines()
        .find_map(|line| {
            line.strip_prefix("rewrites: ")?
                .split_whitespace()
                .next()?
                .parse()
                .ok()
        })
        .unwrap_or_else(|| panic!("missing rewrite count in: {output}"))
}

const META_VARIANT_XOR: &str = r#"
set show timing off .
fmod XOR is
  sort XOR .
  sort Elem .
  ops cst1 cst2 cst3 cst4 : -> Elem .
  subsort Elem < XOR .
  op _+_ : XOR XOR -> XOR [ctor assoc comm] .
  op 0 : -> XOR .
  vars X Y : XOR .
  eq Y + 0 = Y [variant] .
  eq X + X = 0 [variant] .
  eq X + X + Y = Y [variant] .
endfm
fmod META-TEST is
  inc XOR .
  inc META-LEVEL .
endfm
"#;

fn meta_variant_repl() -> Repl {
    let mut r = repl();
    let prelude = r.eval(conformance_file!("prelude-meta.maude")).output;
    assert!(
        !prelude
            .lines()
            .any(|line| line.starts_with("error") || line.starts_with("parse error")),
        "meta prelude: {prelude}"
    );
    let setup = r.eval(META_VARIANT_XOR).output;
    assert!(
        !setup
            .lines()
            .any(|line| line.starts_with("error") || line.starts_with("parse error")),
        "variant meta setup: {setup}"
    );
    r
}

/// Pins incremental numbering, fresh-family selection, continuation state, unifier order, and complete
/// variant matching end to end.
#[test]
fn variant_sequences_and_continuation_follow_contract() {
    let mut r = repl();
    r.eval(
        r#"
fmod IDEM is
  sort S .
  ops a b c : -> S .
  op _*_ : S S -> S [assoc comm] .
  vars X Y : S .
  eq X * X = X [variant] .
endfm
"#,
    );
    let mut output = r.eval("get variants [1] X * Y .").output;
    output.push('\n');
    output.push_str(&r.eval("continue 1 .").output);
    output.push('\n');
    output.push_str(&r.eval("continue 1 .").output);
    output.push('\n');
    output.push_str(&r.eval("variant unify X * a =? Y * b .").output);

    r.eval(
        r#"
fmod FOO is
  sort Foo .
  ops f g : Foo Foo -> Foo .
  op 1f : -> Foo .
  ops x y z : -> Foo .
  vars X Y Z : Foo .
  eq f(X, 1f) = X [variant] .
  eq f(1f, X) = X [variant] .
endfm
"#,
    );
    output.push('\n');
    output.push_str(
        &r.eval("variant match f(X, g(Y, Z)) <=? f(X, g(Y, Z)) .")
            .output,
    );

    assert_eq!(
        variant_sequence_lines(&output),
        [
            "get variants [1] in IDEM : X * Y .",
            "Variant 1",
            "rewrites: 0",
            "S: #1:S * #2:S",
            "X --> #1:S",
            "Y --> #2:S",
            "Variant 2",
            "rewrites: 1",
            "S: %1:S",
            "X --> %1:S",
            "Y --> %1:S",
            "No more variants.",
            "rewrites: 0",
            "variant unify in IDEM : X * a =? Y * b .",
            "Unifier 1",
            "rewrites: 2",
            "X --> b * %1:S",
            "Y --> a * %1:S",
            "Unifier 2",
            "rewrites: 2",
            "X --> b",
            "Y --> a",
            "No more unifiers.",
            "rewrites: 4",
            "variant match in FOO : f(X, g(Y, Z)) <=? f(X, g(Y, Z)) .",
            "rewrites: 1",
            "Matcher 1",
            "X --> X",
            "Y --> Y",
            "Z --> Z",
            "No more matchers.",
        ]
        .map(str::to_string)
    );
}

/// A one-sided identity sends the irredundant filter's subsumption check through frozen
/// unification, which rebuilds each binding; an `iter` count beyond `u64` used to panic there.
#[test]
fn irredundant_unify_keeps_bignum_iter_counts() {
    let out = repl()
        .eval(
            "fmod LID-ITER is
               sort N .
               op z : -> N [ctor] .
               op s_ : N -> N [ctor iter] .
               op g : N N -> N [left id: z] .
               op f : N N -> N [comm] .
             endfm
             irredundant unify f(X:N, s_^18446744073709551617(g(Y:N, Z:N)))
               =? f(s_^18446744073709551617(A:N), B:N) .",
        )
        .output;
    // The same two most-general unifiers as for a small count.
    assert_eq!(out.matches("\nUnifier ").count(), 2, "{out}");
    assert!(
        out.contains("X:N --> s_^18446744073709551617(")
            && out.contains("B:N --> s_^18446744073709551617(g("),
        "{out}"
    );
}

/// Variant narrowing filters redundant steps with the same subsumption check, so `get variants`
/// over a one-sided-identity operator must keep a bignum `iter` count as well.
#[test]
fn get_variants_keeps_bignum_iter_counts() {
    let out = repl()
        .eval(
            "fmod LID-ITER-VARIANTS is
               sort T .
               op e : -> T [ctor] .
               op q_ : T -> T [ctor iter] .
               op h : T T -> T [ctor left id: e] .
               op f : T -> T .
               vars X Y : T .
               eq f(q_^18446744073709551618(h(X, Y))) = Y [variant] .
               eq f(q_^18446744073709551618(X)) = X [variant] .
             endfm
             get variants f(W:T) .",
        )
        .output;
    // `W --> q^n(h(X, Y))` is an instance of `W --> q^n(X)` and is filtered out.
    assert_eq!(out.matches("\nVariant ").count(), 2, "{out}");
    assert!(
        out.contains("W:T --> q_^18446744073709551618(") && out.contains("No more variants."),
        "{out}"
    );
}

/// Cache sequences distinguish forward resume, equal-index reuse, backward restart, terminal-state
/// deletion, and exact four-entry MRU eviction.
#[test]
fn meta_variant_index_cache_preserves_contract() {
    let mut get = meta_variant_repl();
    let get_command =
        |n| format!("red metaGetVariant(['XOR], upTerm(X:XOR + cst1), empty, '#, {n}) .");
    let get_outputs: Vec<String> = [0, 1, 1, 0, 1, 2, 3]
        .into_iter()
        .map(|n| get.eval(&get_command(n)).output)
        .collect();
    assert_eq!(
        get_outputs
            .iter()
            .map(|out| one_rewrite_count(out))
            .collect::<Vec<_>>(),
        [3, 6, 3, 3, 6, 3, 3]
    );
    assert!(
        get_outputs[0].contains(
            "result Variant: {'_+_['cst1.Elem, '%1:XOR], \n  'X:XOR <- '%1:XOR, '%, (none).Parent, false}"
        ),
        "initial tuple: {}",
        get_outputs[0]
    );
    assert!(
        get_outputs[1]
            .contains("result Variant: {'cst1.Elem, \n  'X:XOR <- '0.XOR, '@, (0).Zero, true}"),
        "first child tuple: {}",
        get_outputs[1]
    );
    assert!(
        get_outputs[6].contains(
            "result Variant: {'@1:XOR, \n  'X:XOR <- '_+_['cst1.Elem, '@1:XOR], '@, (0).Zero, false}"
        ),
        "last layer tuple: {}",
        get_outputs[6]
    );

    let mut capacity = meta_variant_repl();
    let capacity_requests = [
        ("cst1", "#"),
        ("cst2", "#"),
        ("cst3", "#"),
        ("cst4", "#"),
        ("cst1", "#"),
        ("cst1", "@"),
        ("cst2", "#"),
        ("cst1", "#"),
    ];
    let capacity_counts: Vec<_> = capacity_requests
        .into_iter()
        .map(|(constant, family)| {
            let command = format!(
                "red metaGetVariant(['XOR], upTerm(X:XOR + {constant}), empty, '{family}, 1) ."
            );
            one_rewrite_count(&capacity.eval(&command).output)
        })
        .collect();
    assert_eq!(capacity_counts, [6, 6, 6, 6, 3, 6, 6, 3]);

    let mut unify = meta_variant_repl();
    let unify_command = |n| {
        format!(
            "red metaVariantUnify(['XOR], upTerm(X:XOR + cst1) =? \
             upTerm(Y:XOR + cst2), empty, '#, none, {n}) ."
        )
    };
    let unify_outputs: Vec<String> = [0, 1, 1, 0, 1]
        .into_iter()
        .map(|n| unify.eval(&unify_command(n)).output)
        .collect();
    assert_eq!(
        unify_outputs
            .iter()
            .map(|out| one_rewrite_count(out))
            .collect::<Vec<_>>(),
        [10, 4, 4, 10, 4]
    );
    assert!(
        unify_outputs[0].contains(
            "'X:XOR <- '_+_['cst2.Elem, '@1:XOR] ; \n  'Y:XOR <- '_+_['cst1.Elem, '@1:XOR], '@}"
        ),
        "first meta unifier: {}",
        unify_outputs[0]
    );
    assert!(
        unify_outputs[1].contains("'X:XOR <- 'cst2.Elem ; \n  'Y:XOR <- 'cst1.Elem, '@}"),
        "second meta unifier: {}",
        unify_outputs[1]
    );

    let match_command = |n| {
        format!(
            "red metaVariantMatch(['XOR], upTerm(cst1 + X:XOR) <=? \
             upTerm(cst2 + Y:XOR), empty, '#, none, {n}) ."
        )
    };
    let match_outputs: Vec<String> = [0, 1, 1, 0, 1]
        .into_iter()
        .map(|n| unify.eval(&match_command(n)).output)
        .collect();
    assert_eq!(
        match_outputs
            .iter()
            .map(|out| one_rewrite_count(out))
            .collect::<Vec<_>>(),
        [7, 4, 7, 7, 4]
    );
    assert!(
        match_outputs[0].contains("'X:XOR <- '_+_['cst1.Elem, 'cst2.Elem, 'Y:XOR]"),
        "meta matcher: {}",
        match_outputs[0]
    );
    assert!(
        match_outputs[1].contains("result Substitution?: (noMatch).Substitution?"),
        "terminal meta match: {}",
        match_outputs[1]
    );
}

/// Associative unifier exhaustion preserves the incompleteness bit after two results rather than returning
/// plain `noUnifier`.
#[test]
fn meta_variant_incomplete_result_preserves_incompleteness() {
    let mut r = meta_variant_repl();
    let output = r
        .eval(
            r#"
fmod A-UNIF is
  sorts List Elt .
  subsort Elt < List .
  op __ : List List -> List [assoc] .
  ops a b c : -> Elt .
  vars A B C : List .
endfm
fmod META-A-TEST is
  inc A-UNIF .
  inc META-LEVEL .
endfm
red metaVariantUnify(['A-UNIF], upTerm(A:List B:List) =?
    upTerm(B:List C:List), empty, '%, none, 2) .
"#,
        )
        .output;
    assert_eq!(one_rewrite_count(&output), 4, "rewrite count: {output}");
    assert!(
        output.contains("result UnificationPair?: (noUnifierIncomplete).UnificationPair?"),
        "associative incompleteness: {output}"
    );
}

/// Reflected op-to-term maps recover both mixfix variable positions when inserted into a child interpreter.
#[test]
fn reflected_mixfix_term_map_survives_child_insert_view() {
    let mut r = repl();
    let prelude = r.eval(conformance_file!("prelude-meta.maude"));
    assert!(
        !prelude.exit && !prelude.output.contains("error in module"),
        "META-LEVEL prelude loads: {}",
        prelude.output
    );
    let stock = r.eval(
        &std::fs::read_to_string(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../share/maude-gpl/metaInterpreter.maude"
        ))
        .expect("read bundled metaInterpreter.maude"),
    );
    assert!(
        !stock.exit && !stock.output.contains("error in module"),
        "stock meta-interpreter loads: {}",
        stock.output
    );
    let output = r
        .eval(
            r#"
set include BOOL off .

fth TNK18-SOURCE is
  sorts Elt Oid Msg .
  op to_from_get : Oid Oid -> Msg .
  op to_from_answer(_) : Oid Oid Elt -> Msg .
endfth

fmod TNK18-TARGET is
  sorts Item Oid Msg .
  op fetch : Oid Oid -> Msg .
  op reply : Oid Oid Item -> Msg .
endfm

view TNK18-VIEW from TNK18-SOURCE to TNK18-TARGET is
  sort Elt to Item .
  vars O O' : Oid .
  var X : Elt .
  msg to O from O' get to term fetch(O, O') .
  msg to O from O' answer(X) to term reply(O, O', X) .
endv

mod TNK18-DRIVER is
  protecting TNK18-SOURCE .
  protecting TNK18-TARGET .
  protecting META-INTERPRETER .

  sort ViewCmd ModuleCmd Seq .
  subsort ViewCmd ModuleCmd < Seq .
  op v : Qid -> ViewCmd .
  op m : Qid -> ModuleCmd .
  op __ : Seq Seq -> Seq [assoc id: nil] .
  op nil : -> Seq .
  op predef : -> Seq .
  eq predef = m('TNK18-SOURCE) m('TNK18-TARGET) v('TNK18-VIEW) .

  op me : -> Oid .
  op User : -> Cid .
  op pending:_ : Seq -> Attribute .

  vars X Y Z : Oid .
  var Q : Qid .
  var Rest : Seq .
  var AS : AttributeSet .

  rl < X : User | pending: (m(Q) Rest), AS > createdInterpreter(X, Y, Z) =>
     < X : User | pending: Rest, AS > insertModule(Z, X, upModule(Q, false)) .
  rl < X : User | pending: (m(Q) Rest), AS > insertedModule(X, Y) =>
     < X : User | pending: Rest, AS > insertModule(Y, X, upModule(Q, false)) .
  rl < X : User | pending: (v(Q) Rest), AS > insertedModule(X, Y) =>
     < X : User | pending: Rest, AS > insertView(Y, X, upView(Q)) .
endm

erewrite in TNK18-DRIVER :
  <> < me : User | pending: predef >
  createInterpreter(interpreterManager, me, none) .
"#,
        )
        .output;

    assert!(
        !output.contains("Bad view.")
            && !output.contains("interpreterError")
            && !output.contains("error in module"),
        "reflected view insertion succeeds: {output}"
    );
    assert!(
        output.contains("rewrites: 7"),
        "reflected view rewrite count: {output}"
    );
    assert!(
        output.contains("insertedView(me, interpreter(0))") && output.contains("pending: nil"),
        "child accepted the reflected mixfix term map: {output}"
    );
}

/// A reflected view's complete term-map matrix survives child insertion and executes every mapped form.
#[test]
fn reflected_term_map_matrix_survives_child_execution() {
    let mut r = repl();
    let prelude = r.eval(conformance_file!("prelude-meta.maude"));
    assert!(
        !prelude.exit && !prelude.output.contains("error in module"),
        "META-LEVEL prelude loads: {}",
        prelude.output
    );
    let stock = r.eval(
        &std::fs::read_to_string(concat!(
            env!("CARGO_MANIFEST_DIR"),
            "/../../share/maude-gpl/metaInterpreter.maude"
        ))
        .expect("read bundled metaInterpreter.maude"),
    );
    assert!(
        !stock.exit && !stock.output.contains("error in module"),
        "stock meta-interpreter loads: {}",
        stock.output
    );
    let fixture = conformance_file!("subsystems/I28-reflected-view-term-maps.maude").replacen(
        "load metaInterpreter\n",
        "",
        1,
    );
    let output = r.eval(&fixture).output;

    assert!(
        !output.contains("Bad view.")
            && !output.contains("interpreterError")
            && !output.contains("error in module"),
        "reflected view and child modules load: {output}"
    );
    assert!(
        output.contains("functional: reducedTerm(me, interpreter(0), 21")
            && output.contains("'probe['s_^6['0.Zero]")
            && output.contains("'s_^16['0.Zero]")
            && output.contains("'s_^4['0.Zero]")
            && output.contains("'s_^5['0.Zero]")
            && output.contains("'s_^26['0.Zero]")
            && output.contains("'s_^37[")
            && output.contains("'aux1.AuxT]"),
        "all functional mappings execute in the child: {output}"
    );
    assert!(
        output.contains("messaging: rewroteTerm(me, interpreter(0),")
            && output.contains("4, '__['done['s_^8['0.Zero]]")
            && output.contains("pending: nil"),
        "both inherited message mappings execute in the child: {output}"
    );
}

/// Context-free cross-kind output retains its classified suffix spelling.
#[test]
fn cross_kind_ill_sorted_suffix_remains_classified() {
    let output = repl()
        .eval(conformance_file!(
            "probes/cross-kind-ill-sorted-output.maude"
        ))
        .output;
    assert!(
        output.contains(
            "reduce in COV002-ILL-SORTED-OUTPUT : (f(a1)).B .\n\
             rewrites: 1\n\
             result B: b"
        ),
        "applicable first profile: {output}"
    );
    assert!(
        output.contains(
            "reduce in COV002-ILL-SORTED-OUTPUT : (f(a2)).[B] .\n\
             rewrites: 0\n\
             result [B]: (f(a2)).[B]"
        ),
        "classified ill-sorted spelling: {output}"
    );
}

/// Timing is never synthesized. Every renderer keeps its observable counts, `set show timing off`
/// stays silent, and requesting unavailable timing reports one explicit warning.
#[test]
fn timing_output_is_count_only_across_command_families() {
    let output = repl()
        .eval(
            r#"set show timing off .
set show timing on .
set show timing off .
smod TIMING-MATRIX is
  sort S .
  ops a b c : -> S [ctor] .
  op pair : S S -> S [ctor] .
  vars X Y : S .
  rl [r1] : a => b .
  rl [r2] : b => c .
  strat step : @ S .
  sd step := r1 .
endsm
red in TIMING-MATRIX : a .
match in TIMING-MATRIX : X:S <=? a .
unify in TIMING-MATRIX : X:S =? a .
rewrite [1] in TIMING-MATRIX : a .
continue 1 .
frewrite [1] in TIMING-MATRIX : pair(a, a) .
search [1] in TIMING-MATRIX : a =>* X:S .
continue 1 .
srewrite in TIMING-MATRIX : a using step .
fmod TIMING-VARIANTS is
  sort S .
  ops a b : -> S [ctor] .
  op _*_ : S S -> S [assoc comm] .
  vars X Y : S .
  eq X * X = X [variant] .
endfm
get variants [1] in TIMING-VARIANTS : X:S * Y:S .
continue 1 .
variant unify in TIMING-VARIANTS : X:S * a =? Y:S * b .
mod TIMING-NARROW is
  sort N .
  op z : -> N .
  op s : N -> N .
  var X : N .
  rl [up] : s(X) => s(s(X)) [narrowing] .
endm
vu-narrow [1] in TIMING-NARROW : s(X:N) =>1 s(s(z)) .
continue 1 ."#,
        )
        .output;

    let timing_warning =
        "warning: timing measurements are unavailable; timing output remains disabled.";
    assert_eq!(output.matches(timing_warning).count(), 1, "{output}");
    for forbidden in ["0ms", "Decision time", "rewrites/second"] {
        assert!(!output.contains(forbidden), "{forbidden}: {output}");
    }
    for header in [
        "reduce in TIMING-MATRIX",
        "match in TIMING-MATRIX",
        "unify in TIMING-MATRIX",
        "rewrite [1] in TIMING-MATRIX",
        "frewrite [1] in TIMING-MATRIX",
        "search [1] in TIMING-MATRIX",
        "srewrite in TIMING-MATRIX",
        "get variants [1] in TIMING-VARIANTS",
        "variant unify in TIMING-VARIANTS",
        "vu-narrow [1] in TIMING-NARROW",
    ] {
        assert!(output.contains(header), "missing `{header}`:\n{output}");
    }
    assert!(
        output.contains(
            "rewrite [1] in TIMING-MATRIX : a .\nrewrites: 1\nresult S: b\n\
             rewrites: 1\nresult S: c"
        ),
        "rewrite continuation counts:\n{output}"
    );
    assert!(
        output.contains("states: 1  rewrites: 0")
            && output.contains("states: 2  rewrites: 1")
            && output.contains("Variant 2\nrewrites: 1")
            && output.contains("No more unifiers.\nrewrites: 4")
            && output.contains("variant unifier:"),
        "count-only search/variant/narrowing output:\n{output}"
    );
}

#[test]
fn memo_attribute_and_controls_warn_without_changing_results() {
    let mut r = repl();
    let source_warning = r
        .eval(
            "fmod MEMO-BASE is\n\
               sort N .\n\
               op z : -> N [ctor] .\n\
               op s : N -> N [ctor] .\n\
               op f : N -> N [memo] .\n\
               var N : N .\n\
               eq f(z) = z .\n\
               eq f(s(N)) = f(N) .\n\
             endfm",
        )
        .output;
    assert_eq!(
        source_warning,
        wrap::auto_wrap(
            "warning: module `MEMO-BASE`, line 5: `[memo]` on operator `f` is recognized but not \
             implemented; evaluation continues without memoization"
        )
    );

    let import_output = r
        .eval(
            "fmod MEMO-LEFT is protecting MEMO-BASE . endfm\n\
             fmod MEMO-RIGHT is protecting MEMO-BASE . endfm\n\
             fmod MEMO-DIAMOND is\n\
               protecting MEMO-LEFT .\n\
               protecting MEMO-RIGHT .\n\
             endfm",
        )
        .output;
    assert!(!import_output.contains("[memo]"), "{import_output}");

    let file_warning = r
        .eval(concat!(
            "load ",
            env!("CARGO_MANIFEST_DIR"),
            "/../../conformance/probes/memo-source-load.maude"
        ))
        .output;
    assert_eq!(
        file_warning,
        wrap::auto_wrap(
            "warning: module `MEMO-FILE`, line 5: `[memo]` on operator `f` is recognized but not \
             implemented; evaluation continues without memoization"
        )
    );
    assert!(
        r.eval("red in MEMO-FILE : f(z) .")
            .output
            .contains("rewrites: 1\nresult N: z")
    );

    let before = r.eval("red in MEMO-DIAMOND : f(s(z)) .").output;
    assert!(before.contains("rewrites: 2\nresult N: z"), "{before}");
    assert_eq!(r.eval("red in MEMO-DIAMOND : f(s(z)) .").output, before);

    let control_warning = "warning: memoization controls are recognized but not implemented; this command has no effect.";
    for control in [
        "set memo on .",
        "set clear memo on .",
        "set clear memo off .",
        "do clear memo .",
        "do clear memo MEMO-DIAMOND .",
    ] {
        assert_eq!(
            r.eval(control).output,
            wrap::auto_wrap(control_warning),
            "{control}"
        );
        assert_eq!(
            r.eval("red in MEMO-DIAMOND : f(s(z)) .").output,
            before,
            "after {control}"
        );
    }
    assert_eq!(r.eval("red in MEMO-DIAMOND : f(s(z)) .").output, before);
}

#[test]
fn unsupported_strategy_forms_fail_directly_and_through_imports() {
    let mut r = repl();
    let setup = r
        .eval(
            "smod UNSUPPORTED-STRAT is\n\
               sort S .\n\
               ops a b c : -> S [ctor] .\n\
               rl [r] : a => b .\n\
               rl [r2] : b => c .\n\
               strats sx sc ok : @ S .\n\
               sd sx := xmatchrew X:S by X using r .\n\
               csd sc := r if a = b .\n\
               sd ok := r .\n\
             endsm\n\
             smod UNSUPPORTED-USE is\n\
               protecting UNSUPPORTED-STRAT .\n\
             endsm",
        )
        .output;
    assert!(setup.is_empty(), "{setup}");

    let pending = r.eval("rewrite [1] in UNSUPPORTED-USE : a .").output;
    assert!(pending.contains("rewrites: 1\nresult S: b"), "{pending}");
    let rejected = r.eval("srewrite in UNSUPPORTED-USE : a using sx .").output;
    assert_eq!(
        rejected,
        wrap::auto_wrap("error: xmatchrew is recognized but not implemented")
    );
    let resumed = r.eval("continue 1 .").output;
    assert!(
        resumed.contains("rewrites: 1\nresult S: c"),
        "continuation after rejected strategy:\n{resumed}"
    );

    for (command, module, strategy, expected) in [
        (
            "srewrite",
            "UNSUPPORTED-STRAT",
            "sx",
            "error: xmatchrew is recognized but not implemented",
        ),
        (
            "dsrewrite",
            "UNSUPPORTED-STRAT",
            "sx",
            "error: xmatchrew is recognized but not implemented",
        ),
        (
            "srewrite",
            "UNSUPPORTED-USE",
            "sx",
            "error: xmatchrew is recognized but not implemented",
        ),
        (
            "dsrewrite",
            "UNSUPPORTED-USE",
            "sx",
            "error: xmatchrew is recognized but not implemented",
        ),
        (
            "srewrite",
            "UNSUPPORTED-STRAT",
            "sc",
            "error: conditional strategy definitions (`csd`) are recognized but not implemented",
        ),
        (
            "srewrite",
            "UNSUPPORTED-USE",
            "sc",
            "error: conditional strategy definitions (`csd`) are recognized but not implemented",
        ),
    ] {
        let output = r
            .eval(&format!("{command} in {module} : a using {strategy} ."))
            .output;
        assert_eq!(output, wrap::auto_wrap(expected));
        assert!(!output.contains("Solution"), "{output}");

        let recovery = r
            .eval(&format!("srewrite in {module} : a using ok ."))
            .output;
        assert!(
            recovery.contains("Solution 1")
                && recovery.contains("rewrites: 1")
                && recovery.contains("result S: b"),
            "strategy recovery after `{command} {strategy}`:\n{recovery}"
        );
    }
}

#[test]
fn statement_and_module_failures_are_actionable_and_recoverable() {
    let mut r = repl();
    assert!(
        r.eval(
            "fmod RECOVER is\n\
               sort S .\n\
               ops a b : -> S [ctor] .\n\
               eq a = b .\n\
             endfm",
        )
        .output
        .is_empty()
    );

    assert_eq!(
        r.eval(
            "fmod RECOVER is\n\
               sort S .\n\
               op a : -> Missing [ctor] .\n\
             endfm",
        )
        .output,
        wrap::auto_wrap("error: module `RECOVER`, line 1: unknown sort `Missing`")
    );
    let preserved = r.eval("red in RECOVER : a .").output;
    assert!(
        preserved.contains("rewrites: 1\nresult S: b"),
        "{preserved}"
    );
    assert!(
        r.eval("fmod RECOVER-USE is protecting RECOVER . endfm")
            .output
            .is_empty()
    );
    assert!(
        r.eval("red in RECOVER-USE : a .")
            .output
            .contains("rewrites: 1\nresult S: b")
    );

    let dropped = r
        .eval(
            "fmod DROP is\n\
               sort S .\n\
               ops a b : -> S [ctor] .\n\
               op f : S -> S .\n\
               var X : S .\n\
               eq f(X) = X [print Z] .\n\
               eq f(a) = b .\n\
             endfm",
        )
        .output;
    assert_eq!(
        dropped,
        wrap::auto_wrap(
            "warning: module `DROP`, line 6: dropped equation: `[print]` item `Z` is not a declared \
             statement variable"
        )
    );
    assert!(
        r.eval("red in DROP : f(a) .")
            .output
            .contains("rewrites: 1\nresult S: b")
    );

    let imported_drop = r
        .eval(
            "fmod DROP-SOURCE is\n\
               sort S .\n\
               ops a b : -> S [ctor] .\n\
               op f : S -> S .\n\
               vars X Y : S .\n\
               eq f(X) = Y .\n\
               eq f(a) = b .\n\
             endfm\n\
             fmod DROP-LEFT is protecting DROP-SOURCE . endfm\n\
             fmod DROP-RIGHT is protecting DROP-SOURCE . endfm\n\
             fmod DROP-DIAMOND is\n\
               protecting DROP-LEFT .\n\
               protecting DROP-RIGHT .\n\
             endfm",
        )
        .output;
    assert_eq!(
        imported_drop,
        wrap::auto_wrap(
            "warning: module `DROP-SOURCE`, line 6: dropped equation: unbound variable in equation \
             right-hand side or condition"
        )
    );
    assert!(
        r.eval("red in DROP-DIAMOND : f(a) .")
            .output
            .contains("rewrites: 1\nresult S: b")
    );

    let unparseable_drop = r
        .eval(
            "fmod DROP-UNPARSEABLE is\n\
               sort S .\n\
               ops a b : -> S [ctor] .\n\
               op f : S -> S .\n\
               eq f(a) = bogus .\n\
               eq f(a) = b .\n\
             endfm",
        )
        .output;
    assert_eq!(
        unparseable_drop,
        wrap::auto_wrap(
            "warning: module `DROP-UNPARSEABLE`, line 5: dropped equation: no parse at token 0 \
             (`bogus`): `bogus`"
        )
    );
    assert!(
        r.eval("red in DROP-UNPARSEABLE : f(a) .")
            .output
            .contains("rewrites: 1\nresult S: b")
    );

    let kind_drops = r
        .eval(
            "mod DROP-KINDS is\n\
               sort S .\n\
               ops a b : -> S [ctor] .\n\
               var X : S .\n\
               mb a : S [print Z] .\n\
               rl a => b [print Z] .\n\
               rl a => b .\n\
             endm",
        )
        .output;
    assert_eq!(
        kind_drops,
        wrap::auto_wrap(
            "warning: module `DROP-KINDS`, line 5: dropped membership: `[print]` item `Z` is not a \
             declared statement variable\n\
             warning: module `DROP-KINDS`, line 6: dropped rule: `[print]` item `Z` is not a \
             declared statement variable"
        )
    );
    assert!(
        r.eval("rewrite [1] in DROP-KINDS : a .")
            .output
            .contains("rewrites: 1\nresult S: b")
    );

    assert_eq!(
        r.eval("fmod NEVER is\n  sort S .\n  op a : -> S .").output,
        wrap::auto_wrap("parse error: module `NEVER`, line 3: unexpected end of input in module")
    );
    assert!(
        r.eval("fmod LATER is sort S . op ok : -> S [ctor] . endfm")
            .output
            .is_empty()
    );
    assert!(
        r.eval("red in LATER : ok .")
            .output
            .contains("rewrites: 0\nresult S: ok")
    );

    assert_eq!(
        r.eval("view BAD from RECOVER to RECOVER is endv").output,
        wrap::auto_wrap("error: view `BAD`, line 1: view `BAD`: source `RECOVER` is not a theory")
    );
    assert!(
        r.eval("red in RECOVER : a .")
            .output
            .contains("rewrites: 1\nresult S: b")
    );
}

#[test]
fn meta_boundaries_distinguish_supported_and_inert_operations() {
    let mut r = repl();
    let prelude = r.eval(conformance_file!("prelude-meta.maude")).output;
    assert!(
        !prelude.contains("error: module") && !prelude.contains("parse error:"),
        "META prelude build:\n{prelude}"
    );
    let output = r
        .eval(
            r#"fmod META-BOUNDARY-MATCH is
  sort S .
  ops a b : -> S [ctor] .
endfm
mod META-BOUNDARY-APPLY is
  sort S .
  ops a b : -> S [ctor] .
  op f : S -> S [ctor] .
  vars X Y : S .
  crl [r] : f(X) => Y if Y := b .
endm
red in META-LEVEL : metaMatch(upModule('META-BOUNDARY-MATCH, false), 'X:S, 'a.S, nil, 0) .
red in META-LEVEL : metaMatch(upModule('META-BOUNDARY-MATCH, false), 'X:S, 'a.S, 'X:S := 'a.S, 0) .
red in META-LEVEL : metaApply(upModule('META-BOUNDARY-APPLY, false), 'f['a.S], 'r, none, 0) .
red in META-LEVEL : metaParseStrategy(['NAT], none, 'top '`( 'all '`)) ."#,
        )
        .output;

    assert!(
        output.contains("result Assignment: \n  'X:S <- 'a.S"),
        "unconditioned metaMatch:\n{output}"
    );
    assert!(
        output.contains("result [Substitution?]: metaMatch("),
        "conditioned metaMatch remains inert:\n{output}"
    );
    assert!(
        output.contains(": metaApply("),
        "conditioned metaApply remains inert:\n{output}"
    );
    assert!(
        output.contains("result [StrategyList,Strategy?]: metaParseStrategy("),
        "strategy META hook remains inert:\n{output}"
    );
    assert!(!output.contains("dropped rule"), "{output}");
    assert!(!output.contains("error:"), "{output}");
}
