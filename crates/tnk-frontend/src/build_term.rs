//! `build_term`: walk a parse [`PTree`] into a kernel [`Term`], and the end-to-end glue that takes a
//! command/term token bubble through lex-built grammar → Earley parse → forest → term → reduce.
//!
//! Each grammar production carries a pre-resolved [`Action`]. The tree walk builds operator
//! applications, flattens associative-list children, assigns statement-local variable indices, keeps
//! iteration counts compact, and forwards pass-through nodes.

use crate::cfparser::compile::CompiledGrammar;
use crate::cfparser::forest::PTree;
use crate::grammar::Action;
use crate::lex::{Interner, Token};
use crate::sig::syntax::BuiltModule;
use tnk_core::dag::DagId;
use tnk_core::engine::Engine;
use tnk_core::smt::SmtNumber;
use tnk_core::sort::SortId;
use tnk_core::symbol::SymbolId;
use tnk_core::term::Term;

/// The base name of a written variable: the text before the first `:` of an on-the-fly `X:Sort` token,
/// or the whole name of a declared variable. Together with the resolved sort it identifies the variable,
/// and it is the name the kernel records on a variable leaf.
pub fn variable_base_name(written: &str) -> &str {
    written.split_once(':').map_or(written, |(base, _)| base)
}

/// Assign each distinct variable a statement-local index. One index is shared across a statement's left
/// side, right side, and condition. A variable is identified by its base name and resolved sort, so
/// every spelling of one variable shares an index: a declared `X : S` and an on-the-fly `X:S`, or the
/// kind spellings `X:[A]` and `X:[B]` of one kind. The first-seen spelling names the slot.
#[derive(Debug, Default, Clone)]
pub struct VarIndex {
    entries: Vec<(String, SortId)>,
}

impl VarIndex {
    pub fn new() -> Self {
        Self::default()
    }

    /// The index for the variable spelled `name` at `sort`, assigning a fresh one in first-seen order.
    pub fn index_of(&mut self, name: &str, sort: SortId) -> u32 {
        if let Some(p) = self.find(name, sort) {
            return p;
        }
        self.entries.push((name.to_string(), sort));
        (self.entries.len() - 1) as u32
    }

    /// The index already assigned to the variable spelled `name` at `sort`, if any. Any spelling with the
    /// same base name and sort finds the same index.
    pub fn find(&self, name: &str, sort: SortId) -> Option<u32> {
        let base = variable_base_name(name);
        self.entries
            .iter()
            .position(|(n, s)| *s == sort && variable_base_name(n) == base)
            .map(|p| p as u32)
    }

    /// The number of distinct variables seen (a statement's `nr_vars`).
    pub fn count(&self) -> u32 {
        self.entries.len() as u32
    }

    /// The first-seen source spelling of the variable at `index` (for rendering a `match` solution's
    /// `X --> …` lines).
    pub fn name(&self, index: u32) -> &str {
        &self.entries[index as usize].0
    }

    /// The declared sort of the variable at `index` — for a `search` solution's `X:Sort --> …` lines,
    /// which (unlike `match`) annotate the variable with its sort.
    pub fn sort(&self, index: u32) -> SortId {
        self.entries[index as usize].1
    }

    /// Reorder slots after theory normalization has fixed the command's canonical variable order.
    pub(crate) fn reorder(&mut self, old_slots: &[usize]) {
        debug_assert_eq!(old_slots.len(), self.entries.len());
        self.entries = old_slots
            .iter()
            .map(|&slot| self.entries[slot].clone())
            .collect();
    }
}

/// Build a kernel [`Term`] from a parse tree. `vars` accumulates the statement-local variable indices
/// (pass a fresh one for a ground command term).
pub fn build_term(
    tree: &PTree,
    g: &CompiledGrammar,
    m: &BuiltModule,
    tokens: &[Token],
    i: &Interner,
    vars: &mut VarIndex,
) -> Result<Term, String> {
    match g.prods[tree.prod as usize].action {
        Action::PassThru => {
            let child = tree.nt_children.first().ok_or("PassThru without a child")?;
            build_term(child, g, m, tokens, i, vars)
        }
        Action::MakeTerm(sym) => {
            let args = make_args(tree, sym, g, m, tokens, i, vars)?;
            Ok(Term::op(sym, args))
        }
        Action::MakeVariable(sort) => {
            let name = tokens[tree.start].text(i);
            Ok(Term::var(vars.index_of(name, sort), sort))
        }
        Action::MakeNatural(succ) => {
            let text = tokens[tree.start].text(i);
            let zero = m.nat_zero.ok_or("MAKE_NATURAL without a zero symbol")?;
            numeral_term(succ, zero, text)
        }
        Action::MakeInteger(minus) => {
            let text = tokens[tree.start].text(i);
            let magnitude = text.strip_prefix('-').unwrap_or(text);
            let succ = m
                .nat_succ
                .ok_or("MAKE_INTEGER without a successor symbol")?;
            let zero = m.nat_zero.ok_or("MAKE_INTEGER without a zero symbol")?;
            Ok(Term::op(minus, vec![numeral_term(succ, zero, magnitude)?]))
        }
        Action::MakeRational { division, minus } => {
            let text = tokens[tree.start].text(i);
            let (neg, num, den) = rational_parts(text)?;
            let succ = m
                .nat_succ
                .ok_or("MAKE_RATIONAL without a successor symbol")?;
            let zero = m.nat_zero.ok_or("MAKE_RATIONAL without a zero symbol")?;
            let numerator = if neg {
                Term::op(minus, vec![numeral_term(succ, zero, num)?])
            } else {
                numeral_term(succ, zero, num)?
            };
            Ok(Term::op(
                division,
                vec![numerator, numeral_term(succ, zero, den)?],
            ))
        }
        Action::MakeSmtNumber { symbol, kind } => {
            let text = tokens[tree.start].text(i);
            let value =
                SmtNumber::parse(text, kind).ok_or_else(|| format!("bad SMT number `{text}`"))?;
            Ok(Term::smt_number(symbol, value))
        }
        Action::MakeIter(sym) => {
            let text = tokens[tree.start].text(i);
            let count = iter_count(text)?;
            let child = tree
                .nt_children
                .first()
                .ok_or("MakeIter without an argument")?;
            let arg = build_term(child, g, m, tokens, i, vars)?;
            Term::iter_decimal(sym, count, arg).ok_or_else(|| format!("bad iter count `{text}`"))
        }
        Action::MakeString(sym) => Ok(Term::string(
            sym,
            &unquote_string(tokens[tree.start].text(i)),
        )),
        Action::MakeQid(sym) => {
            let text = tokens[tree.start].text(i);
            Ok(Term::qid(sym, text.strip_prefix('\'').unwrap_or(text)))
        }
        Action::MakeFloat(sym) => {
            let text = tokens[tree.start].text(i);
            let v: f64 = text.parse().map_err(|_| format!("bad float `{text}`"))?;
            Ok(Term::float(sym, v))
        }
        Action::AssocList => Err("assoc-list node reached build_term directly".to_string()),
        Action::Nop => Err("sort production has no term".to_string()),
    }
}

/// Build a `MakeTerm` argument list, flattening a lone associative-list child into its elements.
fn make_args(
    tree: &PTree,
    _sym: SymbolId,
    g: &CompiledGrammar,
    m: &BuiltModule,
    tokens: &[Token],
    i: &Interner,
    vars: &mut VarIndex,
) -> Result<Vec<Term>, String> {
    if tree.nt_children.len() == 1 && is_assoc_list(g, &tree.nt_children[0]) {
        flatten_assoc(&tree.nt_children[0], g, m, tokens, i, vars)
    } else {
        tree.nt_children
            .iter()
            .map(|c| build_term(c, g, m, tokens, i, vars))
            .collect()
    }
}

/// Flatten a left-recursive associative-list subtree into element terms from left to right.
fn flatten_assoc(
    node: &PTree,
    g: &CompiledGrammar,
    m: &BuiltModule,
    tokens: &[Token],
    i: &Interner,
    vars: &mut VarIndex,
) -> Result<Vec<Term>, String> {
    // Collect right children while walking the left spine, then reverse before building. This preserves
    // source-order variable indexing and therefore observable unification slot and print order.
    let mut subtrees: Vec<&PTree> = Vec::new();
    let mut cur = node;
    loop {
        // An assoc-list production is binary: `<list> ::= <left> , <right>`.
        subtrees.push(&cur.nt_children[1]);
        let left = &cur.nt_children[0];
        if is_assoc_list(g, left) {
            cur = left;
        } else {
            subtrees.push(left);
            break;
        }
    }
    subtrees.reverse();
    subtrees
        .iter()
        .map(|st| build_term(st, g, m, tokens, i, vars))
        .collect()
}

fn is_assoc_list(g: &CompiledGrammar, t: &PTree) -> bool {
    matches!(g.prods[t.prod as usize].action, Action::AssocList)
}

/// Build a compact static `s^count(zero)` term. The arbitrary-size count is scalar [`tnk_core::Nat`]
/// data, so a million-successor identity or statement literal allocates one [`Term::Iter`] plus its
/// zero child rather than a million nested [`Term::Op`] nodes.
fn numeral_term(succ: SymbolId, zero: SymbolId, count: &str) -> Result<Term, String> {
    Term::iter_decimal(succ, count, Term::constant(zero))
        .ok_or_else(|| format!("bad numeral `{count}`"))
}

/// Build `s^count(base)` for the `iter` successor `succ` from a decimal `count`, on the DAG side.
/// The kernel count is a bignum `Nat` natively, so an arbitrary-size numeral
/// (`1267650600228229401496703205376`, `s_^k` at any k) builds in one node.
fn build_iter_dag(
    engine: &mut Engine,
    succ: SymbolId,
    base: DagId,
    count: &str,
) -> Result<DagId, String> {
    engine
        .make_iter_decimal(succ, count, base)
        .ok_or_else(|| format!("bad numeral `{count}`"))
}

/// The decimal count of an `iter`-token `f^count` (the text after the last `^`).
fn iter_count(text: &str) -> Result<&str, String> {
    text.rsplit_once('^')
        .map(|(_, d)| d)
        .ok_or_else(|| format!("iter token `{text}` has no `^count`"))
}

/// The signed numerator and positive denominator of a glued rational literal `[-]num/den`.
fn rational_parts(text: &str) -> Result<(bool, &str, &str), String> {
    let (neg, rest) = match text.strip_prefix('-') {
        Some(r) => (true, r),
        None => (false, text),
    };
    let (num, den) = rest
        .split_once('/')
        .ok_or_else(|| format!("bad rational `{text}`"))?;
    Ok((neg, num, den))
}

/// Build a kernel `DagId` directly from a parse tree — the **ground command-term** path. Unlike
/// [`build_term`] (which yields a `Term` for statements/patterns), this constructs DAG nodes through the
/// engine, so it can build built-in **literals** (string/qid/float values a `Term` cannot carry) and a
/// compact `s^n(0)` numeral (no successor chain). Operators dispatch by theory via [`Engine::make_node`].
/// Variables are rejected — a `reduce` term is ground.
pub fn build_dag(
    tree: &PTree,
    g: &CompiledGrammar,
    engine: &mut Engine,
    nat_zero: Option<SymbolId>,
    nat_succ: Option<SymbolId>,
    tokens: &[Token],
    i: &Interner,
) -> Result<DagId, String> {
    let mut vars = VarIndex::new();
    build_dag_inner(
        tree,
        g,
        engine,
        nat_zero,
        nat_succ,
        tokens,
        i,
        &mut vars,
        DagVarMode::Reject,
    )
}

/// Build a symbolic command DAG directly, keeping variables as genuine logic-variable leaves.
/// Unlike [`build_term`], compact `f^N(arg)` iteration remains one bignum-backed DAG node.
#[allow(clippy::too_many_arguments)]
pub fn build_logic_dag(
    tree: &PTree,
    g: &CompiledGrammar,
    engine: &mut Engine,
    nat_zero: Option<SymbolId>,
    nat_succ: Option<SymbolId>,
    tokens: &[Token],
    i: &Interner,
    vars: &mut VarIndex,
) -> Result<DagId, String> {
    build_dag_inner(
        tree,
        g,
        engine,
        nat_zero,
        nat_succ,
        tokens,
        i,
        vars,
        DagVarMode::Logic,
    )
}

#[derive(Clone, Copy)]
enum DagVarMode {
    Reject,
    Logic,
}

#[allow(clippy::too_many_arguments)]
fn build_dag_inner(
    tree: &PTree,
    g: &CompiledGrammar,
    engine: &mut Engine,
    nat_zero: Option<SymbolId>,
    nat_succ: Option<SymbolId>,
    tokens: &[Token],
    i: &Interner,
    vars: &mut VarIndex,
    variable_mode: DagVarMode,
) -> Result<DagId, String> {
    match g.prods[tree.prod as usize].action {
        Action::PassThru => {
            let child = tree.nt_children.first().ok_or("PassThru without a child")?;
            build_dag_inner(
                child,
                g,
                engine,
                nat_zero,
                nat_succ,
                tokens,
                i,
                vars,
                variable_mode,
            )
        }
        Action::MakeTerm(sym) => {
            let args = dag_args(
                tree,
                g,
                engine,
                nat_zero,
                nat_succ,
                tokens,
                i,
                vars,
                variable_mode,
            )?;
            Ok(engine.make_node(sym, args))
        }
        Action::MakeNatural(succ) => {
            let text = tokens[tree.start].text(i);
            let zero = nat_zero.ok_or("MAKE_NATURAL without a zero symbol")?;
            let base = engine.make_const(zero);
            build_iter_dag(engine, succ, base, text)
        }
        Action::MakeInteger(minus) => {
            let text = tokens[tree.start].text(i);
            let mag = text.strip_prefix('-').unwrap_or(text);
            let zero = nat_zero.ok_or("MAKE_INTEGER without a zero symbol")?;
            let succ = nat_succ.ok_or("MAKE_INTEGER without a successor symbol")?;
            let base = engine.make_const(zero);
            let nat = build_iter_dag(engine, succ, base, mag)?;
            Ok(engine.make_node(minus, vec![nat]))
        }
        Action::MakeRational { division, minus } => {
            let text = tokens[tree.start].text(i);
            let (neg, num, den) = rational_parts(text)?;
            let zero = nat_zero.ok_or("MAKE_RATIONAL without a zero symbol")?;
            let succ = nat_succ.ok_or("MAKE_RATIONAL without a successor symbol")?;
            let base = engine.make_const(zero);
            let num_base = engine.make_const(zero);
            let num_nat = build_iter_dag(engine, succ, num_base, num)?;
            let numerator = if neg {
                engine.make_node(minus, vec![num_nat])
            } else {
                num_nat
            };
            let denominator = build_iter_dag(engine, succ, base, den)?;
            Ok(engine.make_node(division, vec![numerator, denominator]))
        }
        Action::MakeSmtNumber { symbol, kind } => {
            let text = tokens[tree.start].text(i);
            let value =
                SmtNumber::parse(text, kind).ok_or_else(|| format!("bad SMT number `{text}`"))?;
            Ok(engine.make_smt_number(symbol, value))
        }
        Action::MakeIter(sym) => {
            let text = tokens[tree.start].text(i);
            let count = iter_count(text)?;
            let arg = tree
                .nt_children
                .first()
                .ok_or("MakeIter without an argument")?;
            let base = build_dag_inner(
                arg,
                g,
                engine,
                nat_zero,
                nat_succ,
                tokens,
                i,
                vars,
                variable_mode,
            )?;
            build_iter_dag(engine, sym, base, count)
        }
        Action::MakeString(sym) => {
            Ok(engine.make_string(sym, &unquote_string(tokens[tree.start].text(i))))
        }
        Action::MakeQid(sym) => {
            let text = tokens[tree.start].text(i);
            Ok(engine.make_qid(sym, text.strip_prefix('\'').unwrap_or(text)))
        }
        Action::MakeFloat(sym) => {
            let text = tokens[tree.start].text(i);
            let v: f64 = text.parse().map_err(|_| format!("bad float `{text}`"))?;
            Ok(engine.make_float(sym, v))
        }
        Action::MakeVariable(sort) => match variable_mode {
            DagVarMode::Reject => Err("a reduce-command term must be ground (no variables)".into()),
            DagVarMode::Logic => {
                let token = &tokens[tree.start];
                let name = token.text(i);
                let index = vars.index_of(name, sort);
                // Store the base-name token code; the full `X:Sort` token is not the variable identity.
                let base = variable_base_name(name);
                let name = i.get(base).unwrap_or(token.sym).index();
                Ok(engine.make_var(sort, name, index))
            }
        },
        Action::AssocList => Err("assoc-list node reached build_dag directly".into()),
        Action::Nop => Err("a sort production has no term".into()),
    }
}

/// The argument DAGs for a `MakeTerm`: the nonterminal children, flattening a single assoc-list child to
/// the operator's full argument sequence (the `build_term` `make_args` analogue, on the DAG side). A
/// manual loop (not `map`) so the `&mut Engine` reborrows per child.
#[allow(clippy::too_many_arguments)]
fn dag_args(
    tree: &PTree,
    g: &CompiledGrammar,
    engine: &mut Engine,
    nat_zero: Option<SymbolId>,
    nat_succ: Option<SymbolId>,
    tokens: &[Token],
    i: &Interner,
    vars: &mut VarIndex,
    variable_mode: DagVarMode,
) -> Result<Vec<DagId>, String> {
    if tree.nt_children.len() == 1 && is_assoc_list(g, &tree.nt_children[0]) {
        return flatten_dag_assoc(
            &tree.nt_children[0],
            g,
            engine,
            nat_zero,
            nat_succ,
            tokens,
            i,
            vars,
            variable_mode,
        );
    }
    let mut args = Vec::with_capacity(tree.nt_children.len());
    for c in &tree.nt_children {
        args.push(build_dag_inner(
            c,
            g,
            engine,
            nat_zero,
            nat_succ,
            tokens,
            i,
            vars,
            variable_mode,
        )?);
    }
    Ok(args)
}

#[allow(clippy::too_many_arguments)]
fn flatten_dag_assoc(
    node: &PTree,
    g: &CompiledGrammar,
    engine: &mut Engine,
    nat_zero: Option<SymbolId>,
    nat_succ: Option<SymbolId>,
    tokens: &[Token],
    i: &Interner,
    vars: &mut VarIndex,
    variable_mode: DagVarMode,
) -> Result<Vec<DagId>, String> {
    let mut subtrees = Vec::new();
    let mut cur = node;
    loop {
        subtrees.push(&cur.nt_children[1]);
        let left = &cur.nt_children[0];
        if is_assoc_list(g, left) {
            cur = left;
        } else {
            subtrees.push(left);
            break;
        }
    }
    subtrees.reverse();
    let mut args = Vec::with_capacity(subtrees.len());
    for subtree in subtrees {
        args.push(build_dag_inner(
            subtree,
            g,
            engine,
            nat_zero,
            nat_succ,
            tokens,
            i,
            vars,
            variable_mode,
        )?);
    }
    Ok(args)
}

/// Strip a string literal's surrounding quotes and decode its escapes into a raw **byte** value. The
/// lexer retains the quotes, and this function iterates the token text's bytes: `"héllo"` occupies six
/// UTF-8 bytes and therefore yields six value bytes. Backslash-newline is a continuation and removes
/// both bytes. Named control escapes are `\a`(7), `\b`(8), `\f`(12), `\n`, `\r`, `\t`, `\v`(11),
/// `\"`, and `\\`; a 1–3 digit octal escape is truncated to one byte, and any other `\c` yields `c`.
pub fn unquote_string(tok: &str) -> Vec<u8> {
    let inner = tok
        .strip_prefix('"')
        .and_then(|s| s.strip_suffix('"'))
        .unwrap_or(tok);
    let bytes = inner.as_bytes();
    let mut out = Vec::with_capacity(bytes.len());
    let mut i = 0;
    while i < bytes.len() {
        let b = bytes[i];
        if b != b'\\' {
            out.push(b);
            i += 1;
            continue;
        }
        i += 1; // consume the backslash
        let Some(&c) = bytes.get(i) else { break }; // a trailing backslash is dropped
        match c {
            b'\n' => {} // source continuation: Token::fixUp removes the pair
            b'a' => out.push(0x07),
            b'b' => out.push(0x08),
            b'f' => out.push(0x0c),
            b'n' => out.push(b'\n'),
            b'r' => out.push(b'\r'),
            b't' => out.push(b'\t'),
            b'v' => out.push(0x0b),
            b'0'..=b'7' => {
                // Read 1–3 octal digits and truncate the accumulated value to one byte (`\400` → 0).
                let mut val: u32 = 0;
                let mut n = 0;
                while n < 3 && matches!(bytes.get(i), Some(b'0'..=b'7')) {
                    val = val * 8 + u32::from(bytes[i] - b'0');
                    i += 1;
                    n += 1;
                }
                out.push(val as u8);
                continue; // `i` already advanced past the digits
            }
            other => out.push(other), // \" \\ and any other escaped byte → the bare byte
        }
        i += 1;
    }
    out
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::cfparser::{ParseEffort, earley, forest};
    use crate::grammar::{Nt, build::build_grammar};
    use crate::lex::tokenize;
    use crate::sig::build_sig::build_module;
    use crate::surface::parser::Parser;

    const NATB: &str = "\
fmod NATB is
  sorts Truth Zero NzNat Nat .
  subsorts Zero NzNat < Nat .
  ops tt ff : -> Truth [ctor] .
  op 0 : -> Zero [ctor] .
  op s_ : Nat -> NzNat [ctor iter special (id-hook SuccSymbol term-hook zeroTerm (0))] .
  op _+_ : NzNat Nat -> NzNat [assoc comm special (id-hook ACU_NumberOpSymbol (+) op-hook succSymbol (s_ : Nat ~> NzNat))] .
  op _+_ : Nat Nat -> Nat [ditto] .
  op _*_ : NzNat NzNat -> NzNat [assoc comm special (id-hook ACU_NumberOpSymbol (*) op-hook succSymbol (s_ : Nat ~> NzNat))] .
  op _*_ : Nat Nat -> Nat [ditto] .
  op _<_ : Nat Nat -> Truth [special (id-hook NumberOpSymbol (<) op-hook succSymbol (s_ : Nat ~> NzNat) term-hook trueTerm (tt) term-hook falseTerm (ff))] .
  op gcd : NzNat Nat -> NzNat [assoc comm special (id-hook ACU_NumberOpSymbol (gcd) op-hook succSymbol (s_ : Nat ~> NzNat))] .
  op gcd : Nat Nat -> Nat [ditto] .
endfm
";

    /// Parse, build, and reduce a NATB term, reporting its result sort, rewrite count, and equality with
    /// an expected numeral.
    struct Natb {
        m: BuiltModule,
        i: Interner,
        g: CompiledGrammar,
    }

    fn natb() -> Natb {
        built(NATB)
    }

    /// Parse and build the first module of `src` with its compiled grammar.
    fn built(src: &str) -> Natb {
        let mut i = Interner::new();
        let toks = tokenize(src, &mut i);
        let s = Parser::new(&toks, &i).parse_source().expect("parse");
        let m = build_module(&s.modules[0], &mut i).expect("build");
        let g = CompiledGrammar::compile(&build_grammar(&m, &mut i));
        Natb { m, i, g }
    }

    impl Natb {
        /// Parse + build + reduce a ground term; return `(result, rewrites)`.
        fn reduce(&mut self, term: &str) -> (tnk_core::dag::DagId, u64) {
            let tokens = tokenize(term, &mut self.i);
            let mut effort = ParseEffort::default();
            let chart = earley::parse(&self.g, &tokens, Nt::Term, &self.i, &mut effort)
                .expect("parse effort");
            let parse = forest::extract(&self.g, &chart, tokens.len(), Nt::Term, &mut effort)
                .expect("parse");
            assert!(!parse.ambiguous, "`{term}` parsed ambiguously");
            let mut vars = VarIndex::new();
            let t = build_term(&parse.tree, &self.g, &self.m, &tokens, &self.i, &mut vars)
                .expect("build_term");
            let dag = self.m.engine.instantiate(&t, &empty_subst());
            self.m.engine.reset_rewrites();
            let r = self.m.engine.reduce(dag);
            (r, self.m.engine.rewrites())
        }

        /// An expected numeral `s^n(0)` built directly through the engine.
        fn numeral(&mut self, n: u64) -> tnk_core::dag::DagId {
            let z = self.m.engine.make_const(self.m.nat_zero.unwrap());
            self.m.engine.make_iter(self.m.nat_succ.unwrap(), n, z)
        }

        fn sort_name(&self, d: tnk_core::dag::DagId) -> String {
            self.m
                .engine
                .sorts()
                .name(self.m.engine.sort_of(d))
                .to_string()
        }
    }

    fn empty_subst() -> tnk_core::term::Subst {
        let mut s = tnk_core::term::Subst::new();
        s.reset(0);
        s
    }

    /// Parse module text and check arithmetic results against engine-built expected numerals, including
    /// the result sort and rewrite count.
    #[test]
    fn reduces_arithmetic_to_expected_numerals() {
        let mut e = natb();

        let (r, rw) = e.reduce("2 + 3");
        let five = e.numeral(5);
        assert!(e.m.engine.deep_equal(r, five), "2 + 3 = 5");
        assert_eq!(e.sort_name(r), "NzNat");
        assert_eq!(rw, 1, "one ACU_NumberOp rewrite");

        let (r, _) = e.reduce("3 * 4");
        let twelve = e.numeral(12);
        assert!(e.m.engine.deep_equal(r, twelve), "3 * 4 = 12");

        let (r, _) = e.reduce("gcd ( 12 , 18 )");
        let six = e.numeral(6);
        assert!(e.m.engine.deep_equal(r, six), "gcd(12, 18) = 6");
    }

    #[test]
    fn reduces_repeated_successor_and_parens() {
        let mut e = natb();
        // `s s 0` is a ground iter numeral (no rewrites); `(s 0) + (s s 0)` exercises parens + ACU.
        let (r, _) = e.reduce("s s 0");
        let two = e.numeral(2);
        assert!(e.m.engine.deep_equal(r, two), "s s 0 = s^2(0)");

        let (r, _) = e.reduce("( s 0 ) + ( s s 0 )");
        let three = e.numeral(3);
        assert!(e.m.engine.deep_equal(r, three), "(s 0) + (s s 0) = 3");
    }

    #[test]
    fn relational_reduces_to_truth_constant() {
        let mut e = natb();
        let (r, _) = e.reduce("2 < 3");
        assert_eq!(e.sort_name(r), "Truth", "2 < 3 : Truth");
    }

    /// Parse and build an application `term` with a fresh [`VarIndex`]; return its arguments' variable
    /// slots and the index.
    fn arg_slots(e: &mut Natb, term: &str) -> (Vec<u32>, VarIndex) {
        let tokens = tokenize(term, &mut e.i);
        let mut effort = ParseEffort::default();
        let chart =
            earley::parse(&e.g, &tokens, Nt::Term, &e.i, &mut effort).expect("parse effort");
        let parse =
            forest::extract(&e.g, &chart, tokens.len(), Nt::Term, &mut effort).expect("parse");
        assert!(!parse.ambiguous, "`{term}` parsed ambiguously");
        let mut vars = VarIndex::new();
        let t = build_term(&parse.tree, &e.g, &e.m, &tokens, &e.i, &mut vars).expect("build_term");
        let Term::Op { args, .. } = t else {
            panic!("`{term}` is not an application: {t:?}");
        };
        let slots = args
            .iter()
            .map(|arg| match arg {
                Term::Var(v) => v.index,
                other => panic!("`{term}` has a non-variable argument {other:?}"),
            })
            .collect();
        (slots, vars)
    }

    /// A variable is identified by its base name and resolved sort. The declared `X : Q` and the
    /// on-the-fly `X:Q` are one variable whose slot keeps the first-seen spelling; `X:P` has another
    /// sort; and the kind spellings `X:[P]` and `X:[Q]` both name the one `[Q]`-kind variable.
    #[test]
    fn spellings_with_one_base_name_and_sort_share_a_slot() {
        let mut e = built(
            "fmod VARID is sorts P Q . subsort P < Q . op f : Q Q Q -> Q . var X : Q . endfm",
        );
        let (slots, vars) = arg_slots(&mut e, "f(X, X:Q, X:P)");
        assert_eq!(slots, [0, 0, 1]);
        assert_eq!((vars.count(), vars.name(0), vars.name(1)), (2, "X", "X:P"));

        let (slots, vars) = arg_slots(&mut e, "f(X:Q, X, Y:Q)");
        assert_eq!(slots, [0, 0, 1]);
        assert_eq!(vars.name(0), "X:Q", "the first spelling names the slot");
        let q = e.m.sorts["Q"];
        assert_eq!(vars.find("X", q), Some(0));
        assert_eq!(vars.find("Y", q), Some(1));
        assert_eq!(vars.find("Y", e.m.sorts["P"]), None);

        let (slots, vars) = arg_slots(&mut e, "f(X:[P], X:[Q], X)");
        assert_eq!(slots, [0, 0, 1]);
        assert_eq!(
            vars.count(),
            2,
            "the kind variable differs from the declared `X : Q`"
        );
    }

    #[test]
    fn static_prefix_iteration_is_one_bignum_term_node() {
        let mut e = natb();
        let tokens = tokenize("s_^1000000(0)", &mut e.i);
        let mut effort = ParseEffort::default();
        let chart =
            earley::parse(&e.g, &tokens, Nt::Term, &e.i, &mut effort).expect("parse effort");
        let parse = forest::extract(&e.g, &chart, tokens.len(), Nt::Term, &mut effort)
            .expect("parse compact iter");
        assert!(!parse.ambiguous);
        let term = build_term(&parse.tree, &e.g, &e.m, &tokens, &e.i, &mut VarIndex::new())
            .expect("build compact static iter");

        match term {
            Term::Iter { symbol, count, arg } => {
                assert_eq!(Some(symbol), e.m.nat_succ);
                assert_eq!(count.to_decimal(), "1000000");
                assert!(matches!(
                    *arg,
                    Term::Op { symbol, ref args }
                        if Some(symbol) == e.m.nat_zero && args.is_empty()
                ));
            }
            other => panic!("expected one compact static iter node, got {other:?}"),
        }
    }
}
