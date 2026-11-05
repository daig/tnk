use std::io::Write;
use std::path::PathBuf;
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

static NEXT_PATH: AtomicU64 = AtomicU64::new(0);

fn command() -> Command {
    Command::new(env!("CARGO_BIN_EXE_tnk-repl"))
}

fn scratch_path(label: &str) -> PathBuf {
    let timestamp = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .expect("system clock must follow the Unix epoch")
        .as_nanos();
    std::env::temp_dir().join(format!(
        "tnk-repl-{label}-{}-{timestamp}-{}",
        std::process::id(),
        NEXT_PATH.fetch_add(1, Ordering::Relaxed)
    ))
}

#[test]
fn cli_evaluates_stdin_without_a_prelude() {
    let mut child = command()
        .args(["-no-banner", "-no-prelude"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn tnk-repl");

    child
        .stdin
        .take()
        .expect("piped stdin")
        .write_all(
            b"fmod BOOLISH is\n\
                sort Bool .\n\
                ops true false : -> Bool [ctor] .\n\
                op not_ : Bool -> Bool .\n\
                eq not true = false .\n\
                eq not false = true .\n\
              endfm\n\
              reduce not true .\n",
        )
        .expect("write source to tnk-repl");

    let output = child.wait_with_output().expect("wait for tnk-repl");
    assert_eq!(output.status.code(), Some(0));
    assert_eq!(
        String::from_utf8(output.stdout).expect("UTF-8 stdout"),
        "reduce in BOOLISH : not true .\nrewrites: 1\nresult Bool: false\n"
    );
    assert!(output.stderr.is_empty());
}

#[test]
fn cli_reports_argument_and_file_failures_with_distinct_statuses() {
    let unknown = command()
        .arg("-bogus")
        .output()
        .expect("run unknown-option case");
    assert_eq!(unknown.status.code(), Some(2));
    assert!(unknown.stdout.is_empty());
    assert_eq!(
        String::from_utf8(unknown.stderr).expect("UTF-8 stderr"),
        "error: unknown option `-bogus`\n"
    );

    let extra = command()
        .args(["one.maude", "two.maude"])
        .output()
        .expect("run extra-file case");
    assert_eq!(extra.status.code(), Some(2));
    assert!(extra.stdout.is_empty());
    assert_eq!(
        String::from_utf8(extra.stderr).expect("UTF-8 stderr"),
        "error: unexpected argument `two.maude`; only one input file is supported\n"
    );

    let missing = scratch_path("missing.maude");
    let unreadable = command()
        .args(["-no-banner", "-no-prelude"])
        .arg(&missing)
        .output()
        .expect("run missing-file case");
    assert_eq!(unreadable.status.code(), Some(1));
    assert!(unreadable.stdout.is_empty());
    let stderr = String::from_utf8(unreadable.stderr).expect("UTF-8 stderr");
    assert!(
        stderr.starts_with(&format!("error: reading `{}`: ", missing.display())),
        "unexpected diagnostic: {stderr:?}"
    );
}

#[test]
fn missing_optional_prelude_warns_and_exits_successfully() {
    let cwd = scratch_path("empty-cwd");
    std::fs::create_dir(&cwd).expect("create isolated working directory");

    let output = command()
        .arg("-no-banner")
        .env_remove("MAUDE_LIB")
        .current_dir(&cwd)
        .output()
        .expect("run missing-prelude case");

    std::fs::remove_dir(&cwd).expect("remove isolated working directory");
    assert_eq!(output.status.code(), Some(0));
    assert!(output.stdout.is_empty());
    assert_eq!(
        String::from_utf8(output.stderr).expect("UTF-8 stderr"),
        "warning: prelude.maude not found (set MAUDE_LIB or use -no-prelude); continuing without\n"
    );
}

#[test]
fn cli_reports_subsort_cycle_without_panicking() {
    let mut child = command()
        .args(["-no-banner", "-no-prelude"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn tnk-repl");

    child
        .stdin
        .take()
        .expect("piped stdin")
        .write_all(
            b"fmod CYCLIC is\n\
                sorts A B C .\n\
                subsort A < B .\n\
                subsort B < C .\n\
                subsort C < A .\n\
              endfm\n\
              fmod AFTER is\n\
                sort D .\n\
                op d : -> D .\n\
              endfm\n\
              reduce d .\n",
        )
        .expect("write source to tnk-repl");

    let output = child.wait_with_output().expect("wait for tnk-repl");
    let stdout = String::from_utf8(output.stdout).expect("UTF-8 stdout");
    let stderr = String::from_utf8(output.stderr).expect("UTF-8 stderr");
    assert_eq!(output.status.code(), Some(0), "stderr: {stderr}");
    assert!(!stderr.contains("panicked"), "{stderr}");
    assert!(
        stdout.starts_with("error: module `CYCLIC`"),
        "unexpected output: {stdout:?}"
    );
    assert!(
        stdout.ends_with("reduce in AFTER : d .\nrewrites: 0\nresult D: d\n"),
        "unexpected output: {stdout:?}"
    );
}

#[test]
fn cli_drops_bare_variable_equation_without_panicking() {
    let mut child = command()
        .args(["-no-banner", "-no-prelude"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn tnk-repl");

    child
        .stdin
        .take()
        .expect("piped stdin")
        .write_all(
            b"fmod BEFORE is\n\
                sort B .\n\
                op b : -> B .\n\
              endfm\n\
              reduce b .\n\
              fmod BARE is\n\
                sort S .\n\
                ops c d : -> S .\n\
                eq X:S = c .\n\
                eq d = c .\n\
              endfm\n\
              reduce d .\n",
        )
        .expect("write source to tnk-repl");

    let output = child.wait_with_output().expect("wait for tnk-repl");
    let stdout = String::from_utf8(output.stdout).expect("UTF-8 stdout");
    let stderr = String::from_utf8(output.stderr).expect("UTF-8 stderr");
    assert_eq!(output.status.code(), Some(0), "stderr: {stderr}");
    assert!(!stderr.contains("panicked"), "{stderr}");
    assert!(
        stdout.starts_with("reduce in BEFORE : b .\nrewrites: 0\nresult B: b\n"),
        "unexpected output: {stdout:?}"
    );
    assert!(
        stdout.contains("dropped equation: equation left-hand side is a"),
        "unexpected output: {stdout:?}"
    );
    assert!(
        stdout.ends_with("reduce in BARE : d .\nrewrites: 1\nresult S: c\n"),
        "unexpected output: {stdout:?}"
    );
}

/// Run `source` through `tnk-repl -no-banner -no-prelude` on stdin, killing the process if it is still
/// running after `limit`.
fn run_prelude_free_within(source: &str, limit: Duration) -> Output {
    let mut child = command()
        .args(["-no-banner", "-no-prelude"])
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn tnk-repl");
    child
        .stdin
        .take()
        .expect("piped stdin")
        .write_all(source.as_bytes())
        .expect("write source to tnk-repl");
    let deadline = Instant::now() + limit;
    while child.try_wait().expect("poll tnk-repl").is_none() {
        if Instant::now() >= deadline {
            child.kill().expect("kill tnk-repl");
            panic!("tnk-repl did not finish within {limit:?}");
        }
        std::thread::sleep(Duration::from_millis(20));
    }
    child.wait_with_output().expect("collect tnk-repl output")
}

#[test]
fn deep_strategy_recursion_does_not_overflow_the_stack() {
    // `rep(d^14(z), a)` reduces to f(f(...f(a)...)) with 2^14 = 16384 applications of `f`. Each strategy
    // below recurses once per `f`: through a named call, a matchrew by-variable, or a rule's
    // rewrite-condition substrategy. The first three fail at the bottom, so the whole nest is abandoned at
    // once; the last two succeed there and rebuild every level.
    let module = "smod DEEP is\n\
          sorts S D .\n\
          op a : -> S [ctor] .\n\
          op f : S -> S [ctor] .\n\
          op ok : -> S [ctor] .\n\
          op z : -> D [ctor] .\n\
          op d : D -> D [ctor] .\n\
          op rep : D S -> S .\n\
          var N : D .\n\
          vars X Y : S .\n\
          eq rep(z, X) = f(X) .\n\
          eq rep(d(N), X) = rep(N, rep(N, X)) .\n\
          rl [dec] : f(X) => X .\n\
          rl [done] : f(X) => ok .\n\
          crl [down] : f(X) => f(Y) if X => Y .\n\
          strat walk @ S .\n";
    let subject = "rep(d(d(d(d(d(d(d(d(d(d(d(d(d(d(z)))))))))))))), a)";
    let cases = [
        ("top(dec) ; walk", "walk", "No solution."),
        ("matchrew f(X) by X using walk", "walk", "No solution."),
        ("top(down{walk})", "walk", "No solution."),
        (
            "(matchrew f(X) by X using walk) | match a",
            "walk ; top(done)",
            "result S: ok",
        ),
        (
            "top(down{walk}) | match a",
            "walk ; top(done)",
            "result S: ok",
        ),
    ];
    for (definition, strategy, expected) in cases {
        let source = format!(
            "{module}  sd walk := {definition} .\nendsm\nsrewrite {subject} using {strategy} .\n"
        );
        let output = run_prelude_free_within(&source, Duration::from_secs(120));
        let stdout = String::from_utf8(output.stdout).expect("UTF-8 stdout");
        let stderr = String::from_utf8(output.stderr).expect("UTF-8 stderr");
        assert_eq!(
            output.status.code(),
            Some(0),
            "`sd walk := {definition}` exited abnormally; stderr: {stderr}"
        );
        assert!(stderr.is_empty(), "`sd walk := {definition}`: {stderr}");
        assert!(
            stdout.lines().any(|line| line == expected),
            "`sd walk := {definition}` should print `{expected}`: {stdout}"
        );
    }
}
