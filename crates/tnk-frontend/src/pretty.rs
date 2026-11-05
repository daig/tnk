//! The pretty-printer: a reduced `DagNode` → surface text. Two products share one core walk:
//! - [`print_raw`] — a **round-trippable** plain rendering (`parse∘print = id`): emits forms our parser
//!   reads back (decimal numerals, compact `f^N(t)` for iter counts ≥ 2, `- 3` spaced for negation).
//! - [`print_pretty`] — canonical interactive rendering with optional ANSI syntax coloring.
//!
//! The walk is the inverse of the per-module mixfix grammar and parser: parenthesization inverts the
//! Earley prec/gather gate. A subterm of precedence `prec` is wrapped iff the position's gather bound
//! satisfies `required_prec < prec`, with `LEFT_BARE`/`RIGHT_BARE` adjacency capture. The implementation
//! reads only [`SymbolSyntax`] tables and public kernel accessors.

use crate::grammar::{PREFIX_GATHER, prec_gather};
use crate::lex::{Frag, Interner, Sym, tokenize};
use crate::sig::syntax::{BuiltModule, SymbolSyntax};
use std::borrow::Cow;
use std::rc::Rc;
use tnk_core::Nat;
use tnk_core::dag::{DagId, NaValue, NodeRepr};
use tnk_core::smt::SmtNumber;
use tnk_core::sort::KindId;
use tnk_core::symbol::SymbolId;
use tnk_core::term::Term;

/// A sentinel "no precedence constraint / no adjacent capture" — larger than any real precedence
/// (`MAX_PREC = 127`), so `required_prec < prec` and `capture <= gather` never fire against it.
const UNBOUNDED: u32 = u32::MAX;

/// Adjacency-capture context: precedence and kind of the token abutting one side of a subterm.
/// `NONE` represents a top-level or parenthesized position.
#[derive(Clone, Copy)]
struct Cap {
    prec: u32,
    kind: Option<KindId>,
}
const NONE_CAP: Cap = Cap {
    prec: UNBOUNDED,
    kind: None,
};

/// The syntactic category of an emitted token. The raw printer ignores it; the pretty printer uses it
/// for coloring.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Cat {
    /// An operator name fragment / prefix name.
    Op,
    /// A numeric / built-in constant literal.
    Lit,
    /// Structural punctuation (parens, commas).
    Punct,
}

/// META-LEVEL's independently selectable pretty-print flags.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct PrintOptions {
    pub mixfix: bool,
    pub with_parens: bool,
    pub with_sorts: bool,
    pub flat: bool,
    pub format: bool,
    pub number: bool,
    pub rational: bool,
}

const RAW_PRINT_OPTIONS: PrintOptions = PrintOptions {
    mixfix: true,
    with_parens: false,
    with_sorts: false,
    flat: true,
    format: true,
    number: true,
    rational: false,
};

const PRETTY_PRINT_OPTIONS: PrintOptions = PrintOptions {
    mixfix: true,
    with_parens: false,
    with_sorts: false,
    flat: true,
    format: true,
    number: true,
    rational: true,
};

/// Render `d` (a reduced node) as round-trippable plain text: `parse(print_raw(t)) == t`. Iter counts
/// ≥ 2 print in compact power form and negation as `- n`, both forms our parser reads back.
pub fn print_raw(m: &BuiltModule, i: &Interner, d: DagId) -> String {
    Printer {
        m,
        i,
        faithful: false,
        color: false,
        options: RAW_PRINT_OPTIONS,
        vars: &[],
    }
    .render(d)
}

/// Render `d` for interactive display using compact iterations and negated numerals, with optional
/// ANSI syntax coloring.
pub fn print_pretty(m: &BuiltModule, i: &Interner, d: DagId, color: bool) -> String {
    Printer {
        m,
        i,
        faithful: true,
        color,
        options: PRETTY_PRINT_OPTIONS,
        vars: &[],
    }
    .render(d)
}

/// Render a symbolic DAG while naming variable slots from the command's source-variable table.
pub fn print_pretty_with_variables(
    m: &BuiltModule,
    i: &Interner,
    d: DagId,
    variables: &[String],
    color: bool,
) -> String {
    Printer {
        m,
        i,
        faithful: true,
        color,
        vars: variables,
        options: PRETTY_PRINT_OPTIONS,
    }
    .render(d)
}

/// Render a DAG with META-LEVEL's independently selectable [`PrintOptions`].
/// This is deliberately separate from [`print_pretty`]: omitted options expose the underlying syntax
/// rather than silently inheriting the interactive defaults.
pub fn print_with_options(
    m: &BuiltModule,
    i: &Interner,
    d: DagId,
    options: PrintOptions,
) -> String {
    Printer {
        m,
        i,
        faithful: true,
        color: false,
        vars: &[],
        options,
    }
    .render(d)
}
/// Render a DAG as META-LEVEL `QidList` elements. Ordinary layout whitespace is only lexical
/// separation and is discarded; explicit `format` controls survive as `\s`, `\t`, and `\n` Qids.
pub fn print_qid_tokens_with_options(
    m: &BuiltModule,
    i: &mut Interner,
    d: DagId,
    options: PrintOptions,
) -> Vec<String> {
    let chunks = {
        let printer = Printer {
            m,
            i,
            faithful: true,
            color: false,
            vars: &[],
            options,
        };
        printer.render_qid_chunks(d)
    };
    let mut result = Vec::new();
    for chunk in chunks {
        match chunk {
            QidChunk::Text(text) => {
                for token in tokenize(&text, i) {
                    result.push(i.resolve(token.sym).to_string());
                }
            }
            QidChunk::Control(control) => result.push(control.to_string()),
        }
    }
    result
}

/// Render a static [`Term`] through the same precedence/gather walk as DAG rendering. Variables use
/// statement-local names from `vars`; traces use this for equation and membership bodies.
pub fn print_term(m: &BuiltModule, i: &Interner, t: &Term, vars: &[String], color: bool) -> String {
    Printer {
        m,
        i,
        faithful: true,
        color,
        vars,
        options: PRETTY_PRINT_OPTIONS,
    }
    .print_term_top(t)
}

/// The shared printer. `m`, `i`, and flags are immutable; recursive layout receives the output buffer
/// separately so it can read `self` while appending. One mode selects compact interactive leaf forms
/// instead of parser-oriented forms; `color` enables ANSI syntax coloring; `vars` supplies variable names
/// for a [`Term`] walk and is empty for a DAG walk.
struct Printer<'a> {
    m: &'a BuiltModule,
    i: &'a Interner,
    faithful: bool,
    color: bool,
    vars: &'a [String],
    options: PrintOptions,
}

/// A child to lay out in either walk: a reduced DAG node, or a static [`Term`] (pattern) node. Unifies the
/// DAG printer (`print_raw`/`print_pretty`) and the `Term` printer (`print_term`, for the trace) under one
/// iterative driver.
#[derive(Clone)]
enum Item<'t> {
    Dag(DagId),
    Term(&'t Term),
    /// A virtual right-associated tail over one flattened associative DAG node.
    AssocDag {
        symbol: SymbolId,
        children: Rc<[DagId]>,
        offset: usize,
    },
}

/// One pending unit of output on the explicit work stack. Replacing recursive `print`/`print_app` descent
/// with this stack means a deep subject such as `fib(22)`'s `s^17711(0)` tower cannot overflow the call
/// stack. `Text` is colored output, `Space` is raw inter-token space, and `Visit` is expanded by
/// [`Printer::layout`].
enum Work<'a, 't> {
    Text {
        cat: Cat,
        text: Cow<'a, str>,
    },
    Space,
    /// An explicit `s` format directive (distinct from ordinary lexical separation for `QidList` output).
    FormatSpace,
    /// An explicit `t` format directive.
    Tab,
    /// A `format`-attribute newline (`n`) — `\n` with no trailing space.
    Newline,
    /// A `format`-attribute indent (`i`) — spaces to the current indentation level.
    Indent,
    /// A `format`-attribute indent-level change (`+`/`-`) — no output, shifts later `Indent`s.
    IndentDelta(i32),
    Visit {
        item: Item<'t>,
        req_prec: u32,
        lcap: Cap,
        rcap: Cap,
        range_known: bool,
        top_level: bool,
    },
}

enum QidChunk {
    Text(String),
    Control(&'static str),
}

impl<'a> Printer<'a> {
    fn render(&self, d: DagId) -> String {
        let mut out = String::new();
        self.run_stack(&mut out, Item::Dag(d));
        out
    }

    fn render_qid_chunks(&self, d: DagId) -> Vec<QidChunk> {
        self.run_qid_stack(Item::Dag(d))
    }

    /// Print a static [`Term`] (a pattern, with named variables) — the trace's `eq lhs = rhs .` renderer.
    fn print_term_top(&self, t: &Term) -> String {
        let mut out = String::new();
        self.run_stack(&mut out, Item::Term(t));
        out
    }

    /// Drive the explicit work stack: pop a unit and emit text or expand a node into more work.
    /// [`layout`](Self::layout) yields a node's pieces in forward order; pushing them in reverse lets a
    /// LIFO `pop` replay them and their descendants in emission order. Keeping traversal state in this
    /// heap `Vec` makes arbitrarily deep subjects stack-safe.
    fn run_stack<'t>(&self, out: &mut String, start: Item<'t>) {
        // No context supplies the top-level term's range, so an ambiguous top-level constant receives a
        // sort qualifier.
        let mut stack: Vec<Work<'a, 't>> = vec![Work::Visit {
            item: start,
            req_prec: UNBOUNDED,
            lcap: NONE_CAP,
            rcap: NONE_CAP,
            range_known: false,
            top_level: true,
        }];
        let mut pieces: Vec<Work<'a, 't>> = Vec::new();
        // The `format`-attribute indentation level (in spaces), shifted by `+`/`-` directives as the walk
        // proceeds; an `Indent` emits this many spaces. `+`/`-` are balanced within each format op, so it
        // returns to 0 between top-level pieces.
        let mut indent: i32 = 0;
        while let Some(w) = stack.pop() {
            match w {
                Work::Text { cat, text } => self.emit(out, cat, &text),
                Work::Space | Work::FormatSpace => out.push(' '),
                Work::Tab => out.push('\t'),
                Work::Newline => out.push('\n'),
                Work::Indent => {
                    for _ in 0..indent.max(0) {
                        out.push(' ');
                    }
                }
                Work::IndentDelta(d) => indent += d,
                Work::Visit {
                    item,
                    req_prec,
                    lcap,
                    rcap,
                    range_known,
                    top_level,
                } => {
                    self.layout(
                        item,
                        req_prec,
                        lcap,
                        rcap,
                        range_known,
                        top_level,
                        &mut pieces,
                    );
                    stack.extend(pieces.drain(..).rev());
                }
            }
        }
    }

    /// The META `QidList` variant of [`run_stack`](Self::run_stack): default spaces stay in text chunks
    /// for the lexer to discard, while explicit format controls become first-class Qids.
    fn run_qid_stack<'t>(&self, start: Item<'t>) -> Vec<QidChunk> {
        let mut stack: Vec<Work<'a, 't>> = vec![Work::Visit {
            item: start,
            req_prec: UNBOUNDED,
            lcap: NONE_CAP,
            rcap: NONE_CAP,
            range_known: false,
            top_level: true,
        }];
        let mut pieces: Vec<Work<'a, 't>> = Vec::new();
        let mut chunks = Vec::new();
        let mut text = String::new();
        let mut indent: i32 = 0;
        while let Some(w) = stack.pop() {
            match w {
                Work::Text { cat, text: piece } => self.emit(&mut text, cat, &piece),
                Work::Space => text.push(' '),
                Work::FormatSpace => {
                    flush_qid_text(&mut chunks, &mut text);
                    chunks.push(QidChunk::Control("\\s"));
                }
                Work::Tab => {
                    flush_qid_text(&mut chunks, &mut text);
                    chunks.push(QidChunk::Control("\\t"));
                }
                Work::Newline => {
                    flush_qid_text(&mut chunks, &mut text);
                    chunks.push(QidChunk::Control("\\n"));
                }
                Work::Indent => {
                    flush_qid_text(&mut chunks, &mut text);
                    for _ in 0..indent.max(0) {
                        chunks.push(QidChunk::Control("\\s"));
                    }
                }
                Work::IndentDelta(d) => indent += d,
                Work::Visit {
                    item,
                    req_prec,
                    lcap,
                    rcap,
                    range_known,
                    top_level,
                } => {
                    self.layout(
                        item,
                        req_prec,
                        lcap,
                        rcap,
                        range_known,
                        top_level,
                        &mut pieces,
                    );
                    stack.extend(pieces.drain(..).rev());
                }
            }
        }
        flush_qid_text(&mut chunks, &mut text);
        chunks
    }

    /// Lay out one node into its forward piece sequence, emitting `Text`/`Space` and pushing each child as
    /// a `Visit` without recursing into children.
    #[allow(clippy::too_many_arguments)]
    fn layout<'t>(
        &self,
        item: Item<'t>,
        req_prec: u32,
        lcap: Cap,
        rcap: Cap,
        range_known: bool,
        top_level: bool,
        out: &mut Vec<Work<'a, 't>>,
    ) {
        match item {
            Item::Term(Term::Var(v)) => {
                let name = self
                    .vars
                    .get(v.index as usize)
                    .map(String::as_str)
                    .unwrap_or("_");
                out.push(Work::Text {
                    cat: Cat::Op,
                    text: Cow::Borrowed(name),
                });
            }
            Item::Term(Term::Op { symbol, args }) => {
                // A `nat_succ` tower over `nat_zero` folds to decimal form: `f(2)`, not `f(s s 0)`.
                // Static terms may mix ordinary unary `Op` layers with compact `Iter` runs; both
                // contribute to the rendered decimal.
                if let Some(dec) = self.term_nat_decimal(*symbol, args) {
                    out.push(Work::Text {
                        cat: Cat::Lit,
                        text: Cow::Owned(dec),
                    });
                } else {
                    // A trace pattern has no inferred sort for disambiguation, so its children retain
                    // `range_known = true` and are not qualified independently.
                    let children: Vec<Item> = args.iter().map(Item::Term).collect();
                    self.layout_app(*symbol, &children, req_prec, lcap, rcap, true, out);
                }
            }
            Item::Term(Term::Iter { symbol, count, arg }) => {
                let count = count.to_decimal();
                if self.m.nat_succ == Some(*symbol) && self.is_zero_term(arg) {
                    out.push(Work::Text {
                        cat: Cat::Lit,
                        text: Cow::Owned(count),
                    });
                } else {
                    self.layout_iter(
                        *symbol,
                        &count,
                        Item::Term(arg),
                        req_prec,
                        lcap,
                        rcap,
                        true,
                        out,
                    );
                }
            }
            // A built-in `Term` literal uses the DAG leaf renderer.
            Item::Term(Term::Na { symbol, value }) => {
                let text = match value {
                    NaValue::Str(s) => render_string(s),
                    NaValue::Qid(q) => render_qid(q),
                    NaValue::Float(bits) => render_float(f64::from_bits(*bits)),
                    NaValue::SmtNum(number) => self.smt_number_text(*symbol, number),
                };
                out.push(Work::Text {
                    cat: Cat::Lit,
                    text: Cow::Owned(text),
                });
            }
            Item::AssocDag {
                symbol,
                children,
                offset,
            } => {
                let tail = if offset + 2 == children.len() {
                    Item::Dag(children[offset + 1])
                } else {
                    Item::AssocDag {
                        symbol,
                        children: Rc::clone(&children),
                        offset: offset + 1,
                    }
                };
                let nested = [Item::Dag(children[offset]), tail];
                self.layout_app(symbol, &nested, req_prec, lcap, rcap, true, out);
            }
            Item::Dag(d) => self.layout_dag(d, req_prec, lcap, rcap, range_known, top_level, out),
        }
    }

    /// Lay out one DAG node: a leaf (numeral, string, qid, or float), an `iter`, or an application,
    /// including compact interactive minus and rational forms. Node borrows are released before child
    /// layout by extracting owned leaf data and then fetching a fresh child list.
    #[allow(clippy::too_many_arguments)]
    fn layout_dag<'t>(
        &self,
        d: DagId,
        req_prec: u32,
        lcap: Cap,
        rcap: Cap,
        range_known: bool,
        top_level: bool,
        out: &mut Vec<Work<'a, 't>>,
    ) {
        let symbol = self.m.engine.node(d).symbol();
        let leaf = {
            let node = self.m.engine.node(d);
            match node.repr() {
                NodeRepr::App => None,
                // A count-1 iteration that does not print as a numeral is the ordinary application
                // `f(t)`, so the application path lays it out, including its overload qualification;
                // only numerals and the compact `f^N(t)` form are iteration-specific.
                NodeRepr::Iter { count, arg }
                    if count == "1"
                        && !(self.options.number
                            && self.m.nat_succ == Some(symbol)
                            && self.is_zero(arg)) =>
                {
                    None
                }
                NodeRepr::Iter { count, arg } => Some(Leaf::Iter { count, arg }),
                NodeRepr::Str(s) => Some(Leaf::Atom {
                    text: render_string(s),
                    constant: true,
                    collides: self.m.overloaded_strings.contains(s),
                }),
                NodeRepr::Qid(q) => Some(Leaf::Atom {
                    text: render_qid(q),
                    constant: true,
                    collides: self.m.overloaded_qids.contains(q),
                }),
                NodeRepr::Float(f) => Some(Leaf::Atom {
                    text: render_float(f),
                    constant: true,
                    collides: self.m.overloaded_floats.contains(&f.to_bits()),
                }),
                NodeRepr::SmtNum(number) => Some(Leaf::Atom {
                    text: self.smt_number_text(symbol, number),
                    constant: true,
                    collides: false,
                }),
                // A symbolic variable leaf renders as `base:Sort`. Only generated `#n`, `%n`, and `@n`
                // variables survive into printed unifiers, and each carries its sort.
                NodeRepr::Var { name } => {
                    let base = node
                        .variable_index()
                        .and_then(|slot| self.vars.get(slot as usize))
                        .map(String::as_str)
                        .unwrap_or_else(|| self.i.resolve(crate::lex::Sym::from_raw(name)));
                    let text = if base.contains(':') {
                        base.to_string()
                    } else if matches!(base.as_bytes().first(), Some(b'#' | b'%' | b'@')) {
                        format!(
                            "{}:{}",
                            base,
                            self.m.engine.sorts().name(self.m.engine.sort_of(d))
                        )
                    } else {
                        base.to_string()
                    };
                    Some(Leaf::Atom {
                        text,
                        constant: false,
                        collides: false,
                    })
                }
            }
        };
        match leaf {
            Some(Leaf::Atom {
                text,
                constant,
                collides,
            }) => {
                // A literal whose value a nullary operator also spells (`op "hi" : -> Foo`) is
                // ambiguous with that constant unless context fixes the range; the top level counts.
                let disambiguate =
                    constant && (self.options.with_sorts || (!range_known && collides));
                self.layout_literal(d, text, disambiguate, out);
            }
            Some(Leaf::Iter { count, arg }) => {
                // A natural numeral is a pseudo-literal. In an unknown-range context it needs a qualifier
                // only when multiple kinds provide integer syntax or a nullary user operator has the same
                // numeric spelling.
                let need_disambig = self.options.with_sorts
                    || (!top_level
                        && !range_known
                        && self.m.nat_succ == Some(symbol)
                        && self.is_zero(arg)
                        && (self.m.integer_literal_kind_count > 1
                            || self.m.overloaded_naturals.contains(&count)));
                if need_disambig
                    && self.options.number
                    && self.m.nat_succ == Some(symbol)
                    && self.is_zero(arg)
                {
                    self.layout_literal(d, count.clone(), true, out);
                } else {
                    // `f^N(t)` parses as any `iter` operator named `f`; those lie in different kinds, so
                    // when another one exists only context or a qualified argument selects the kind.
                    let arg_rk = range_known || !self.shares_iter_name(symbol);
                    self.layout_iter(
                        symbol,
                        &count,
                        Item::Dag(arg),
                        req_prec,
                        lcap,
                        rcap,
                        arg_rk,
                        out,
                    );
                }
            }
            None => {
                let children: Vec<DagId> = self.m.engine.node(d).children().collect();
                // Interactive mode prints a negated positive numeral compactly; raw mode uses normal mixfix
                // negation so its output reparses.
                if self.faithful
                    && self.options.number
                    && self.m.minus_sym == Some(symbol)
                    && children.len() == 1
                    && let Some(dec) = self.pos_nat_decimal(children[0])
                {
                    self.layout_literal(d, format!("-{dec}"), self.options.with_sorts, out);
                    return;
                }
                // A rational division node over integer numerals prints compactly as `num/den`. Zero
                // uses a distinct constant rather than a numeral, so `0 / 5` keeps generic spacing.
                if self.options.rational
                    && self.m.division_sym == Some(symbol)
                    && children.len() == 2
                    && let Some(rat) = self.rational_text(children[0], children[1])
                {
                    self.layout_literal(d, rat, self.options.with_sorts, out);
                    return;
                }
                // An ad-hoc-overloaded or literal-spelled symbol whose range is not determined by context
                // receives a `(term).Sort` qualification so output round-trips. `with-sorts` qualifies all
                // constants.
                let need_disambig = (!range_known && self.ambiguous(symbol))
                    || (self.options.with_sorts && children.is_empty());
                let arg_rk = self.range_of_args_known(symbol, range_known, need_disambig);
                if need_disambig {
                    out.push(Work::Text {
                        cat: Cat::Punct,
                        text: Cow::Borrowed("("),
                    });
                }
                let nested_prefix = !self.options.flat
                    && self.m.syntax.get(&symbol).is_some_and(|syn| {
                        syn.assoc
                            && syn.arity() == 2
                            && children.len() > 2
                            && (!self.options.mixfix
                                || !syn.frags.iter().any(|f| matches!(f, Frag::Hole)))
                    });
                if nested_prefix {
                    let children: Rc<[DagId]> = children.into();
                    let items = [
                        Item::Dag(children[0]),
                        Item::AssocDag {
                            symbol,
                            children: Rc::clone(&children),
                            offset: 1,
                        },
                    ];
                    self.layout_app(symbol, &items, req_prec, lcap, rcap, arg_rk, out);
                } else {
                    let items: Vec<Item> = children.iter().map(|&c| Item::Dag(c)).collect();
                    self.layout_app(symbol, &items, req_prec, lcap, rcap, arg_rk, out);
                }
                if need_disambig {
                    let sort = self.qualifier_sort(d);
                    out.push(Work::Text {
                        cat: Cat::Punct,
                        text: Cow::Owned(format!(").{sort}")),
                    });
                }
            }
        }
    }

    /// The sort named by `d`'s `(term).Sort` qualifier. A qualifier selects the parse in its sort's kind
    /// and the grammar spells it only with a user sort, so the error sort's `[K]` name would not reparse.
    /// A kind-level term (least sort = its kind's error sort) is instead qualified by its top symbol's
    /// declared non-error range that comes first in the kind's index order (supersorts first) or, when
    /// every declaration is kind-level (a `poly` range, `~>`, an explicit `[K]` range), by the kind's
    /// first maximal sort.
    fn qualifier_sort(&self, d: DagId) -> &'a str {
        let sorts = self.m.engine.sorts();
        let sort = self.m.engine.sort_of(d);
        if !sorts.sort(sort).is_error {
            return sorts.name(sort);
        }
        let chosen = self
            .m
            .engine
            .symbol_declarations(self.m.engine.node(d).symbol())
            .into_iter()
            .map(|(_, range)| range)
            .filter(|&range| !sorts.sort(range).is_error)
            .min_by_key(|&range| sorts.component_index(range))
            .or_else(|| sorts.kind(sorts.kind_of(sort)).index_order.get(1).copied())
            .unwrap_or(sort);
        sorts.name(chosen)
    }

    fn layout_literal<'t>(
        &self,
        d: DagId,
        text: String,
        disambiguate: bool,
        out: &mut Vec<Work<'a, 't>>,
    ) {
        if disambiguate {
            out.push(Work::Text {
                cat: Cat::Punct,
                text: Cow::Borrowed("("),
            });
        }
        out.push(Work::Text {
            cat: Cat::Lit,
            text: Cow::Owned(text),
        });
        if disambiguate {
            let sort = self.qualifier_sort(d);
            out.push(Work::Text {
                cat: Cat::Punct,
                text: Cow::Owned(format!(").{sort}")),
            });
        }
    }

    /// Lay out an application from its symbol + already-extracted child [`Item`]s: prefix/constant, or a
    /// mixfix form with the prec/gather parenthesization (the inverse of the parser's gather gate, plus the
    /// adjacency-capture cases). Shared by the DAG and `Term` walks.
    #[allow(clippy::too_many_arguments)]
    fn layout_app<'t>(
        &self,
        symbol: SymbolId,
        children: &[Item<'t>],
        req_prec: u32,
        lcap: Cap,
        rcap: Cap,
        arg_rk: bool,
        out: &mut Vec<Work<'a, 't>>,
    ) {
        let command_arguments = self.m.engine.symbol(symbol).is_meta_operation();
        if !self.options.mixfix {
            let cat = if children.is_empty() {
                Cat::Lit
            } else {
                Cat::Op
            };
            self.layout_prefix_name(
                Cow::Borrowed(self.m.engine.symbol(symbol).name()),
                self.m.syntax.get(&symbol),
                cat,
                out,
            );
            if !children.is_empty() {
                self.layout_arg_list(children, arg_rk, command_arguments, out);
            }
            return;
        }
        let Some(syn) = self.m.syntax.get(&symbol) else {
            // No recorded syntax (should not happen for a user op): prefix-print with the kernel name.
            self.layout_prefix_name(
                Cow::Borrowed(self.m.engine.symbol(symbol).name()),
                None,
                Cat::Op,
                out,
            );
            if !children.is_empty() {
                self.layout_arg_list(children, arg_rk, command_arguments, out);
            }
            return;
        };
        let has_hole = syn.frags.iter().any(|f| matches!(f, Frag::Hole));
        if !has_hole {
            // Constants and prefix operators can span multiple lexical fragments. Emit default spacing:
            // preserve glued brackets and inter-token blanks in names.
            let cat = if children.is_empty() {
                Cat::Lit
            } else {
                Cat::Op
            };
            let mut name = String::new();
            let mut no_space = true;
            for f in &syn.frags {
                let text = self.frag_cow(f);
                let special = matches!(&*text, "(" | ")" | "[" | "]" | "{" | "}");
                if !(no_space || special || &*text == ",") {
                    name.push(' ');
                }
                name.push_str(&text);
                no_space = special;
            }
            self.layout_prefix_name(Cow::Owned(name), Some(syn), cat, out);
            if !children.is_empty() {
                self.layout_arg_list(children, arg_rk, command_arguments, out);
            }
            return;
        }
        let pg = prec_gather::compute(
            &syn.frags,
            syn.domain.len(),
            syn.prec,
            syn.gather.as_deref(),
            syn.assoc,
        );
        let paren = self.options.with_parens
            || req_prec < pg.prec
            || self.captures(syn, &pg.gather, lcap, rcap);
        if paren {
            out.push(Work::Text {
                cat: Cat::Punct,
                text: Cow::Borrowed("("),
            });
        }
        // Parentheses block inherited left and right adjacency capture.
        let (lcap, rcap) = if paren {
            (NONE_CAP, NONE_CAP)
        } else {
            (lcap, rcap)
        };
        self.layout_mixfix(
            symbol,
            syn,
            &pg,
            children,
            lcap,
            rcap,
            arg_rk,
            command_arguments,
            out,
        );
        if paren {
            out.push(Work::Text {
                cat: Cat::Punct,
                text: Cow::Borrowed(")"),
            });
        }
    }

    fn layout_prefix_name<'t>(
        &self,
        text: Cow<'a, str>,
        syntax: Option<&SymbolSyntax>,
        cat: Cat,
        out: &mut Vec<Work<'a, 't>>,
    ) {
        let format = if self.options.format {
            syntax
                .and_then(|syn| syn.format.as_deref())
                .filter(|f| f.len() == 2 && format_supported(f))
        } else {
            None
        };
        emit_gap(format.map(|f| f[0].as_str()), false, out);
        out.push(Work::Text { cat, text });
        if let Some(format) = format {
            emit_gap(Some(format[1].as_str()), false, out);
        }
    }

    /// Lay out a mixfix form: walk the syntax fragments, emitting literal tokens and pushing each argument
    /// hole as a `Visit` (at its gather bound + adjacency context). An associative operator with more
    /// arguments than its arity folds its flattened children over the infix tokens (`a + b + c`).
    #[allow(clippy::too_many_arguments)]
    fn layout_mixfix<'t>(
        &self,
        _symbol: SymbolId,
        syn: &SymbolSyntax,
        pg: &prec_gather::PrecGather,
        children: &[Item<'t>],
        lcap: Cap,
        rcap: Cap,
        arg_rk: bool,
        command_arguments: bool,
        out: &mut Vec<Work<'a, 't>>,
    ) {
        let nr_args = syn.domain.len();
        let left_bare = matches!(syn.frags.first(), Some(Frag::Hole));
        let right_bare = matches!(syn.frags.last(), Some(Frag::Hole));

        // Associative fold for the pure binary infix `_ OP _` with > 2 flattened children (the DAG case;
        // a `Term` pattern is nested binary, so prec/gather alone handles `a + b + c`). The between-section
        // (mid fragments + the gap before the next element) repeats per element, with the same default
        // spacing as the binary path — and the same `format`-attribute override (the META `__`
        // declaration/trace lists put each element on a new line, `format (d ni d)` / `(d n d)`).
        if syn.assoc && nr_args == 2 && left_bare && right_bare && children.len() > 2 {
            let format = if self.options.format {
                syn.format
                    .as_deref()
                    .filter(|f| f.len() == syn.frags.len() + 1 && format_supported(f))
            } else {
                None
            };
            let m = syn.frags.len() - 1; // the trailing Hole's index (`f0`/`f_m` are the two arg holes)
            emit_gap(format.map(|f| f[0].as_str()), false, out); // leading gap (before the first element)
            for (idx, c) in children.iter().enumerate() {
                if idx > 0 {
                    let mut no_space = false; // just emitted the previous element
                    for k in 1..m {
                        let text = self.frag_cow(&syn.frags[k]);
                        let special = matches!(&*text, "(" | ")" | "[" | "]" | "{" | "}");
                        emit_gap(
                            format.map(|f| f[k].as_str()),
                            !(no_space || special || &*text == ","),
                            out,
                        );
                        out.push(Work::Text { cat: Cat::Op, text });
                        no_space = special;
                    }
                    emit_gap(format.map(|f| f[m].as_str()), !no_space, out); // gap before the next element
                }
                // A flattened associative node prints as a left fold: every element except the final
                // right operand occupies the left gather position; only the final element uses gather[1].
                let bound = if idx + 1 == children.len() {
                    pg.gather[1]
                } else {
                    pg.gather[0]
                };
                let range_known =
                    arg_rk || (command_arguments && self.is_nonzero_nat_item(c.clone()));
                out.push(Work::Visit {
                    item: c.clone(),
                    req_prec: bound,
                    lcap: NONE_CAP,
                    rcap: NONE_CAP,
                    range_known,
                    top_level: false,
                });
            }
            if let Some(f) = format {
                emit_gap(Some(f[m + 1].as_str()), false, out); // trailing gap
            }
            return;
        }

        // Default mixfix spacing inserts a space before each fragment except at the start, before a
        // comma, around brackets, or between a literal label and its following colon. Colons between
        // argument holes remain spaced.
        // Thus `<_,_>` prints `< M, N >`, not `< M , N >`. With a
        // `format` attribute (the META result/declaration constructors — `_<-_`, `rl_=>_[_].`, …): one
        // directive word per **gap** (before each fragment, plus a trailing one), where `d` is exactly that
        // default, `s`/`n`/`i`/`+`/`-` the explicit space/newline/indent/level. An op whose format uses a
        // directive we don't model (`r`/`o`, on some IO/array ops) falls back to the default.
        let format = if self.options.format {
            syn.format
                .as_deref()
                .filter(|f| f.len() == syn.frags.len() + 1 && format_supported(f))
        } else {
            None
        };
        let object_colons = matches!(
            syn.frags.first(),
            Some(Frag::Tok(symbol)) if self.i.resolve(*symbol) == "<"
        ) && syn
            .frags
            .iter()
            .any(|frag| matches!(frag, Frag::Tok(symbol) if self.i.resolve(*symbol) == "|"));
        // Attribute constructors preserve whether their declaration spelled `label:_` compactly or
        // separated the label from `:_`; object notation exposes that source-level distinction.
        let spaced_label_colons = syn.spaced_label_colon;
        let mut k = 0;
        let mut no_space = true;
        for (pos, frag) in syn.frags.iter().enumerate() {
            let word = format.map(|f| f[pos].as_str());
            match frag {
                Frag::Tok(s) => {
                    let text = self.i.resolve(*s);
                    let special = matches!(text, "(" | ")" | "[" | "]" | "{" | "}");
                    let label_colon = text == ":"
                        && matches!(
                            pos.checked_sub(1).and_then(|p| syn.frags.get(p)),
                            Some(Frag::Tok(_))
                        );
                    let default_space = if spaced_label_colons && text == ":" {
                        true
                    } else if object_colons && text == ":" {
                        matches!(
                            pos.checked_sub(1).and_then(|p| syn.frags.get(p)),
                            Some(Frag::Hole)
                        )
                    } else if label_colon {
                        false
                    } else {
                        !(no_space || special || text == ",")
                    };
                    emit_gap(word, default_space, out);
                    out.push(Work::Text {
                        cat: Cat::Op,
                        text: Cow::Borrowed(text),
                    });
                    no_space = special || ((object_colons || spaced_label_colons) && text == ":");
                }
                Frag::Hole => {
                    let after_object_colon = (object_colons || spaced_label_colons)
                        && matches!(
                            pos.checked_sub(1).and_then(|p| syn.frags.get(p)),
                            Some(Frag::Tok(symbol)) if self.i.resolve(*symbol) == ":"
                        );
                    emit_gap(word, after_object_colon || !no_space, out);
                    let (lc, rc) =
                        self.hole_caps(syn, pg, k, nr_args, left_bare, right_bare, lcap, rcap, pos);
                    let range_known = arg_rk
                        || (command_arguments && self.is_nonzero_nat_item(children[k].clone()));
                    out.push(Work::Visit {
                        item: children[k].clone(),
                        req_prec: pg.gather[k],
                        lcap: lc,
                        rcap: rc,
                        range_known,
                        top_level: false,
                    });
                    k += 1;
                    no_space = false;
                }
            }
        }
        // The trailing gap (after the last fragment): only its non-spacing directives matter (the `--` that
        // closes `_<-_`'s indent). A trailing default contributes nothing (no following token).
        if let Some(f) = format {
            emit_gap(Some(f[syn.frags.len()].as_str()), false, out);
        }
    }

    /// Adjacency-capture contexts for argument hole `k`: a bare end abuts this operator's token, and
    /// outer capture flows through the opposite side.
    #[allow(clippy::too_many_arguments)]
    fn hole_caps(
        &self,
        syn: &SymbolSyntax,
        pg: &prec_gather::PrecGather,
        k: usize,
        nr_args: usize,
        left_bare: bool,
        right_bare: bool,
        lcap: Cap,
        rcap: Cap,
        _pos: usize,
    ) -> (Cap, Cap) {
        let sorts = self.m.engine.sorts();
        if k == 0 && left_bare {
            let rc = Cap {
                prec: pg.prec,
                kind: Some(sorts.kind_of(syn.domain[0])),
            };
            (lcap, rc)
        } else if k == nr_args - 1 && right_bare {
            let lc = Cap {
                prec: pg.prec,
                kind: Some(sorts.kind_of(syn.domain[nr_args - 1])),
            };
            (lc, rcap)
        } else {
            (NONE_CAP, NONE_CAP)
        }
    }

    /// Whether `symbol` needs a range qualifier when context does not provide one: another symbol shares
    /// its name and domain kinds, so arguments alone cannot select the declaration; or it is a nullary
    /// operator whose name this module's grammar also reads as a literal, so its bare spelling denotes
    /// that literal too.
    fn ambiguous(&self, symbol: SymbolId) -> bool {
        self.m
            .overload
            .get(&symbol)
            .is_some_and(|f| f & crate::sig::syntax::OVL_DOMAIN != 0)
            || self.m.literal_named_constants.contains(&symbol)
    }

    /// Whether another `iter` operator shares `symbol`'s name, so `symbol^N(t)` alone does not fix the
    /// kind of `t`.
    fn shares_iter_name(&self, symbol: SymbolId) -> bool {
        self.m
            .overload
            .get(&symbol)
            .is_some_and(|f| f & crate::sig::syntax::OVL_ITER != 0)
    }

    /// Whether argument ranges are known. Ad-hoc overloading leaves them unknown unless context or an
    /// emitted range qualifier pins the operator.
    fn range_of_args_known(
        &self,
        symbol: SymbolId,
        range_known: bool,
        range_disambiguated: bool,
    ) -> bool {
        use crate::sig::syntax::{OVL_ADHOC, OVL_RANGE};
        let f = self.m.overload.get(&symbol).copied().unwrap_or(0);
        if f & OVL_ADHOC == 0 {
            return true; // not overloaded ⇒ argument kinds are determined
        }
        f & OVL_RANGE == 0 && (range_known || range_disambiguated)
    }

    /// Whether an abutting same-kind token can capture a bare operator end under its gather bound.
    fn captures(&self, syn: &SymbolSyntax, gather: &[u32], lcap: Cap, rcap: Cap) -> bool {
        let sorts = self.m.engine.sorts();
        let nr_args = syn.domain.len();
        let left_bare = matches!(syn.frags.first(), Some(Frag::Hole));
        let right_bare = matches!(syn.frags.last(), Some(Frag::Hole));
        (left_bare && lcap.prec <= gather[0] && lcap.kind == Some(sorts.kind_of(syn.domain[0])))
            || (right_bare
                && rcap.prec <= gather[nr_args - 1]
                && rcap.kind == Some(sorts.kind_of(syn.domain[nr_args - 1])))
    }

    /// Lay out `symbol^count(arg)`. A successor over zero becomes decimal. Counts of at least two use
    /// compact `f^N(arg)` form, whose argument inherits `arg_range_known`; count one uses the operator's
    /// ordinary mixfix or prefix syntax.
    #[allow(clippy::too_many_arguments)]
    fn layout_iter<'t>(
        &self,
        symbol: SymbolId,
        count: &str,
        arg: Item<'t>,
        req_prec: u32,
        lcap: Cap,
        rcap: Cap,
        arg_range_known: bool,
        out: &mut Vec<Work<'a, 't>>,
    ) {
        if self.options.number && self.m.nat_succ == Some(symbol) && self.is_zero_item(arg.clone())
        {
            out.push(Work::Text {
                cat: Cat::Lit,
                text: Cow::Owned(count.to_string()),
            });
            return;
        }
        if count != "1" {
            let power = format!("{}^{count}", self.canonical_name(symbol));
            self.layout_prefix_name(Cow::Owned(power), self.m.syntax.get(&symbol), Cat::Op, out);
            out.push(Work::Text {
                cat: Cat::Punct,
                text: Cow::Borrowed("("),
            });
            out.push(Work::Visit {
                item: arg,
                req_prec: PREFIX_GATHER,
                lcap: NONE_CAP,
                rcap: NONE_CAP,
                range_known: arg_range_known,
                top_level: false,
            });
            out.push(Work::Text {
                cat: Cat::Punct,
                text: Cow::Borrowed(")"),
            });
            return;
        }
        self.layout_app(symbol, &[arg], req_prec, lcap, rcap, true, out);
    }

    /// `(a, b, …)` — a prefix argument list (shared by both walks). `arg_rk` is the arguments' inherited
    /// `range_known` (false propagates disambiguation into them under an ad-hoc-overloaded operator).
    fn layout_arg_list<'t>(
        &self,
        children: &[Item<'t>],
        arg_rk: bool,
        command_arguments: bool,
        out: &mut Vec<Work<'a, 't>>,
    ) {
        out.push(Work::Text {
            cat: Cat::Punct,
            text: Cow::Borrowed("("),
        });
        for (idx, c) in children.iter().enumerate() {
            if idx > 0 {
                out.push(Work::Text {
                    cat: Cat::Punct,
                    text: Cow::Borrowed(","),
                });
                out.push(Work::Space);
            }
            let range_known = arg_rk || (command_arguments && self.is_nonzero_nat_item(c.clone()));
            out.push(Work::Visit {
                item: c.clone(),
                req_prec: PREFIX_GATHER,
                lcap: NONE_CAP,
                rcap: NONE_CAP,
                range_known,
                top_level: false,
            });
        }
        out.push(Work::Text {
            cat: Cat::Punct,
            text: Cow::Borrowed(")"),
        });
    }

    /// Nonzero Nat literals in META command arguments remain bare. Zero is an ordinary constant and
    /// receives `(0).Zero` disambiguation when required.
    fn is_nonzero_nat_item(&self, item: Item<'_>) -> bool {
        match item {
            Item::Dag(d) => {
                let node = self.m.engine.node(d);
                self.m.nat_succ == Some(node.symbol())
                    && matches!(node.repr(), NodeRepr::Iter { arg, .. } if self.is_zero(arg))
            }
            Item::Term(Term::Iter { symbol, arg, .. }) => {
                self.m.nat_succ == Some(*symbol) && self.is_zero_term(arg)
            }
            Item::Term(_) | Item::AssocDag { .. } => false,
        }
    }

    /// Whether `arg` is the module's zero constant (so a successor over it is a numeral).
    fn is_zero(&self, arg: DagId) -> bool {
        self.m.nat_zero == Some(self.m.engine.node(arg).symbol())
    }

    fn is_zero_term(&self, arg: &Term) -> bool {
        matches!(
            arg,
            Term::Op { symbol, args } if self.m.nat_zero == Some(*symbol) && args.is_empty()
        )
    }

    fn is_zero_item(&self, arg: Item<'_>) -> bool {
        match arg {
            Item::Dag(d) => self.is_zero(d),
            Item::Term(t) => self.is_zero_term(t),
            Item::AssocDag { .. } => false,
        }
    }

    fn frag_text(&self, frag: &Frag) -> &str {
        match frag {
            Frag::Tok(s) => self.tok_text(*s),
            Frag::Hole => "_",
        }
    }

    /// A fragment's text as a `Cow` borrowing the interner for the printer's lifetime `'a`, so it can sit on
    /// the work-stack outliving the `&self` call that produced it (an argument hole renders as `_`).
    fn frag_cow(&self, frag: &Frag) -> Cow<'a, str> {
        match frag {
            Frag::Tok(s) => Cow::Borrowed(self.i.resolve(*s)),
            Frag::Hole => Cow::Borrowed("_"),
        }
    }
    fn tok_text(&self, s: Sym) -> &str {
        self.i.resolve(s)
    }

    /// An operator's canonical (prefix) name — its fragments concatenated (`[Tok(s), Hole]` → `"s_"`).
    fn canonical_name(&self, symbol: SymbolId) -> String {
        match self.m.syntax.get(&symbol) {
            Some(syn) => syn.frags.iter().map(|f| self.frag_text(f)).collect(),
            None => self.m.engine.symbol(symbol).name().to_string(),
        }
    }

    fn smt_number_text(&self, symbol: SymbolId, number: &SmtNumber) -> String {
        let range = self.m.syntax[&symbol].range;
        let kind = self
            .m
            .engine
            .smt_type(range)
            .expect("SMT number symbol without range metadata");
        number.to_maude(kind)
    }

    /// Return compact `num/den` text when the denominator is a positive numeral and the numerator is a
    /// positive or negated numeral. Zero numerators fall back to generic mixfix rendering.
    fn rational_text(&self, num: DagId, den: DagId) -> Option<String> {
        let d = self.pos_nat_decimal(den)?;
        let n = self.signed_numeral(num)?;
        Some(format!("{n}/{d}"))
    }

    /// Return the decimal value of a strictly positive `s^count(0)` numeral.
    fn pos_nat_decimal(&self, d: DagId) -> Option<String> {
        let node = self.m.engine.node(d);
        match node.repr() {
            NodeRepr::Iter { count, arg }
                if self.m.nat_succ == Some(node.symbol()) && self.is_zero(arg) =>
            {
                Some(count)
            }
            _ => None,
        }
    }

    /// The decimal of a strictly-positive natural numeral pattern: any mix of unary `nat_succ`
    /// applications and compact [`Term::Iter`] runs, bottoming at `nat_zero`. Iterative and bignum-backed,
    /// so neither a deep explicit tower nor a million-count compact run overflows or truncates.
    fn term_nat_decimal(&self, symbol: SymbolId, args: &[Term]) -> Option<String> {
        if self.m.nat_succ != Some(symbol) || args.len() != 1 {
            return None;
        }
        let mut count = Nat::one();
        let mut cur = &args[0];
        loop {
            match cur {
                Term::Op { symbol: s, args } if self.m.nat_succ == Some(*s) && args.len() == 1 => {
                    count = count.add(&Nat::one());
                    cur = &args[0];
                }
                Term::Iter {
                    symbol: s,
                    count: n,
                    arg,
                } if self.m.nat_succ == Some(*s) => {
                    count = count.add(n);
                    cur = arg;
                }
                Term::Op { symbol: s, args } if self.m.nat_zero == Some(*s) && args.is_empty() => {
                    return Some(count.to_decimal());
                }
                _ => return None,
            }
        }
    }

    /// The signed decimal of a nonzero integer numeral: a positive nat `s^n(0)` → `n`, or a negated nat
    /// `-(s^n(0))` → `-n`. `None` for `0` or any non-numeral.
    fn signed_numeral(&self, d: DagId) -> Option<String> {
        if let Some(n) = self.pos_nat_decimal(d) {
            return Some(n);
        }
        let symbol = self.m.engine.node(d).symbol();
        if self.m.minus_sym == Some(symbol) {
            let children: Vec<DagId> = self.m.engine.node(d).children().collect();
            if let [only] = children.as_slice() {
                return self.pos_nat_decimal(*only).map(|n| format!("-{n}"));
            }
        }
        None
    }

    /// Append `text` for category `cat`, wrapping it in `cat`'s ANSI color when `color` is on.
    fn emit(&self, out: &mut String, cat: Cat, text: &str) {
        if self.color {
            out.push_str(cat.ansi());
            out.push_str(text);
            out.push_str(ANSI_RESET);
        } else {
            out.push_str(text);
        }
    }
}

/// Whether every directive in `format` is one the printer interprets (`d s t n i + -`). If not — an `r`/`o`
/// or numeric directive, used by a few IO/array ops — the operator falls back to default spacing rather
/// than mis-render, so a partial format model never produces wrong output.
fn format_supported(format: &[String]) -> bool {
    format.iter().all(|w| {
        w.chars()
            .all(|c| matches!(c, 'd' | 's' | 't' | 'n' | 'i' | '+' | '-'))
    })
}

/// Push the [`Work`] for one `format` gap (or the no-format default if `word` is `None`): `d` is the
/// default space (`default_space`), `s` a space, `t` a tab, `n` a newline, `i` an indent to the current
/// level, `+`/`-` a level change. A multi-directive word (`n++i`, `ni`) emits each in turn.
fn emit_gap<'a, 't>(word: Option<&str>, default_space: bool, out: &mut Vec<Work<'a, 't>>) {
    let Some(w) = word else {
        if default_space {
            out.push(Work::Space);
        }
        return;
    };
    for c in w.chars() {
        match c {
            'd' if default_space => out.push(Work::Space),
            's' => out.push(Work::FormatSpace),
            't' => out.push(Work::Tab),
            'n' => out.push(Work::Newline),
            'i' => out.push(Work::Indent),
            '+' => out.push(Work::IndentDelta(1)),
            '-' => out.push(Work::IndentDelta(-1)),
            _ => {} // `d` with no default space, or a directive excluded by format selection
        }
    }
}

/// ANSI reset.
const ANSI_RESET: &str = "\x1b[0m";

impl Cat {
    /// ANSI SGR color for the terminal syntax-highlighting palette.
    fn ansi(self) -> &'static str {
        match self {
            Cat::Op => "\x1b[33m",    // operators: yellow
            Cat::Lit => "\x1b[36m",   // numeric / constant literals: cyan
            Cat::Punct => "\x1b[90m", // parens/commas: bright black (dim)
        }
    }
}

/// Owned leaf rendering data, extracted from a node's `repr` so the borrow is released before recursion.
enum Leaf {
    Iter {
        count: String,
        arg: DagId,
    },
    /// `collides` marks a literal whose value a nullary operator of the module also spells.
    Atom {
        text: String,
        constant: bool,
        collides: bool,
    },
}

fn flush_qid_text(chunks: &mut Vec<QidChunk>, text: &mut String) {
    if !text.is_empty() {
        chunks.push(QidChunk::Text(std::mem::take(text)));
    }
}

/// Render a quoted identifier with a leading `'` and canonical token-name escapes.
fn render_qid(q: &str) -> String {
    let mut out = String::with_capacity(q.len() + 1);
    out.push('\'');
    let mut escaped = false;
    for c in q.chars() {
        match c {
            '`' => {
                if !escaped {
                    out.push('`');
                }
                escaped = true;
            }
            ' ' => {
                if !escaped {
                    out.push('`');
                }
                escaped = true;
            }
            '(' | ')' | '[' | ']' | '{' | '}' | ',' => {
                if !escaped {
                    out.push('`');
                }
                out.push(c);
                escaped = false;
            }
            _ => {
                out.push(c);
                escaped = false;
            }
        }
    }
    out
}

/// Render raw string bytes in quotes. Printable ASCII is emitted directly except for quote and
/// backslash; named control characters use short escapes, and every other byte uses three-digit octal.
pub fn render_string(s: &[u8]) -> String {
    let mut out = String::with_capacity(s.len() + 2);
    out.push('"');
    for &b in s {
        match b {
            b'"' => out.push_str("\\\""),
            b'\\' => out.push_str("\\\\"),
            0x20..=0x7e => out.push(b as char), // printable ASCII, verbatim
            0x07 => out.push_str("\\a"),
            0x08 => out.push_str("\\b"),
            0x0c => out.push_str("\\f"),
            b'\n' => out.push_str("\\n"),
            b'\r' => out.push_str("\\r"),
            b'\t' => out.push_str("\\t"),
            0x0b => out.push_str("\\v"),
            _ => {
                // 0x00–0x06, 0x0E–0x1F, 0x7F, 0x80–0xFF → 3-digit octal.
                out.push('\\');
                out.push((b'0' + b / 64) as char);
                out.push((b'0' + (b / 8) % 8) as char);
                out.push((b'0' + b % 8) as char);
            }
        }
    }
    out.push('"');
    out
}

/// Render a float through the kernel's canonical formatter, shared with `string(Float)`.
pub fn render_float(f: f64) -> String {
    tnk_core::double_to_string(f)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lex::tokenize;
    use crate::load::{load_source, parse_command_term, reduce_command};
    use crate::surface::ast::Command;

    /// Round-trip every fixture command's reduced result through raw printing and reparsing. The printed
    /// text must parse uniquely, as a match pattern or statement term requires, and denote the same term.
    fn round_trips(src: &str) {
        let mut loaded = load_source(src).expect("load");
        let cmds: Vec<(usize, Vec<crate::lex::Token>)> = loaded
            .commands
            .iter()
            .map(|(m, c)| match c {
                Command::Reduce { term, .. } => (*m, term.clone()),
                _ => panic!("fixture uses only reduce"),
            })
            .collect();
        for (idx, (m, term)) in cmds.iter().enumerate() {
            let parsed = parse_command_term(&loaded.modules[*m], &loaded.interner, term)
                .unwrap_or_else(|e| panic!("command {idx}: {e}"));
            let (result, _) = reduce_command(&mut loaded.modules[*m], &loaded.interner, &parsed)
                .unwrap_or_else(|e| panic!("command {idx}: {e}"));
            let printed = print_raw(&loaded.modules[*m].built, &loaded.interner, result);
            // Re-lex + re-reduce the printed form; it must denote the same term.
            let toks = tokenize(&printed, &mut loaded.interner);
            let reparsed_term = parse_command_term(&loaded.modules[*m], &loaded.interner, &toks)
                .unwrap_or_else(|e| panic!("command {idx} reparse of `{printed}`: {e}"));
            reparsed_term
                .unambiguous_tree(&loaded.interner)
                .unwrap_or_else(|e| panic!("command {idx} reparse of `{printed}`: {e}"));
            let (reparsed, _) =
                reduce_command(&mut loaded.modules[*m], &loaded.interner, &reparsed_term)
                    .unwrap_or_else(|e| panic!("command {idx} reparse of `{printed}`: {e}"));
            let eng = &loaded.modules[*m].built.engine;
            assert!(
                eng.deep_equal(result, reparsed),
                "command {idx}: `{printed}` did not round-trip"
            );
        }
    }

    macro_rules! file {
        ($n:expr) => {
            include_str!(concat!(
                env!("CARGO_MANIFEST_DIR"),
                "/../../conformance/",
                $n
            ))
        };
    }

    #[test]
    fn iter_round_trips() {
        round_trips(file!("iter.maude"));
    }
    #[test]
    fn bool_round_trips() {
        round_trips(file!("bool.maude"));
    }
    #[test]
    fn nat_round_trips() {
        round_trips(file!("nat.maude"));
    }
    #[test]
    fn int_round_trips() {
        round_trips(file!("int.maude"));
    }

    // Exercise raw printing for object syntax, ACU residues, prefix operators, and lowered memberships.
    #[test]
    fn peano_round_trips() {
        round_trips(file!("peano.maude"));
    }
    #[test]
    fn strat_round_trips() {
        round_trips(file!("strat.maude"));
    }
    #[test]
    fn acu_overload_round_trips() {
        round_trips(file!("acu-overload.maude"));
    }
    #[test]
    fn acu_reduce_round_trips() {
        round_trips(file!("acu-reduce.maude"));
    }
    #[test]
    fn membership_round_trips() {
        round_trips(file!("membership.maude"));
    }
    #[test]
    fn overload_round_trips() {
        round_trips(file!("overload.maude"));
    }

    /// Assert exact uncolored result rendering, including ACU order.
    fn renders_as(src: &str, expected: &[&str]) {
        let mut loaded = load_source(src).expect("load");
        let cmds: Vec<(usize, Vec<crate::lex::Token>)> = loaded
            .commands
            .iter()
            .map(|(m, c)| match c {
                Command::Reduce { term, .. } => (*m, term.clone()),
                _ => panic!("fixture uses only reduce"),
            })
            .collect();
        assert_eq!(cmds.len(), expected.len(), "command count");
        for (idx, ((m, term), want)) in cmds.iter().zip(expected).enumerate() {
            let parsed = parse_command_term(&loaded.modules[*m], &loaded.interner, term)
                .unwrap_or_else(|e| panic!("command {idx}: {e}"));
            let (result, _) = reduce_command(&mut loaded.modules[*m], &loaded.interner, &parsed)
                .unwrap_or_else(|e| panic!("command {idx}: {e}"));
            let got = print_pretty(&loaded.modules[*m].built, &loaded.interner, result, false);
            assert_eq!(&got.as_str(), want, "command {idx}");
        }
    }

    #[test]
    fn iter_results_render_expected_forms() {
        renders_as(file!("iter.maude"), &["0", "s 0", "s 0", "s 0", "s 0"]);
    }
    /// An ad-hoc-overloaded constant (`nil` in two kinds) renders as `(nil).Sort` at top level so it can
    /// be reparsed, while a unique constant (`a`) remains bare.
    #[test]
    fn disambiguates_top_level_overloaded_constants() {
        renders_as(
            file!("correctness-disambig.maude"),
            &["(nil).A", "(nil).B", "a"],
        );
    }

    /// Nullary operators spelled as string, quoted-identifier, and float tokens beside those literal
    /// families.
    const LITERAL_NAMED: &str = r#"fmod LITERAL-NAMED is
  sorts Str Qid Flt Foo .
  op <Strings> : -> Str [special (id-hook StringSymbol)] .
  op <Qids> : -> Qid [special (id-hook QuotedIdentifierSymbol)] .
  op <Floats> : -> Flt [special (id-hook FloatSymbol)] .
  op "hi" : -> Foo .
  op 'hi : -> Foo .
  op 1.5 : -> Foo .
  op wrap : Foo -> Foo .
  op pair : Foo Foo -> Foo .
  op pair : Str Str -> Str .
endfm
red ("hi").Foo .
red ("hi").Str .
red ('hi).Foo .
red ('hi).Qid .
red (1.5).Foo .
red (1.5).Flt .
red wrap("hi") .
red pair(("hi").Str, "lo") .
red "lo" .
"#;

    /// A literal-spelled constant and the literal it spells share one bare spelling, so both print
    /// `(t).Sort` wherever context does not fix the range, the top level included. An argument whose
    /// kind is fixed (`wrap`) and a literal that no operator spells stay bare.
    #[test]
    fn qualifies_literal_spelled_constants_and_their_literals() {
        renders_as(
            LITERAL_NAMED,
            &[
                r#"("hi").Foo"#,
                r#"("hi").Str"#,
                "('hi).Foo",
                "('hi).Qid",
                "(1.5).Foo",
                "(1.5).Flt",
                r#"wrap("hi")"#,
                r#"pair(("hi").Str, "lo")"#,
                r#""lo""#,
            ],
        );
        round_trips(LITERAL_NAMED);
    }

    /// Numeral-spelled constants collide only with numeral families whose literal production exists.
    /// `0` is the zero constant rather than a numeral token, `00` matches no numeral terminal, and a
    /// rational or string spelling has no literal production here, so those stay bare.
    #[test]
    fn qualifies_numeral_spelled_constants_by_literal_terminal() {
        let src = r#"fmod NUMERAL-NAMED is
  sorts Zero NzNat Nat NzInt Int Foo .
  subsorts Zero NzNat < Nat .
  subsorts NzNat < NzInt .
  subsorts Nat NzInt < Int .
  op 0 : -> Zero [ctor] .
  op s_ : Nat -> NzNat [ctor iter special (id-hook SuccSymbol term-hook zeroTerm (0))] .
  op -_ : NzNat -> NzInt [ctor special (id-hook MinusSymbol op-hook succSymbol (s_ : Nat ~> NzNat) op-hook minusSymbol (-_ : NzNat ~> Int))] .
  op -_ : Int -> Int [ditto] .
  op 42 : -> Foo .
  op -3 : -> Foo .
  op 00 : -> Foo .
  op 1/2 : -> Foo .
  op "s" : -> Foo .
  op pair : Foo Foo -> Foo .
  op pair : Nat Nat -> Nat .
endfm
red (42).Foo .
red (-3).Foo .
red pair((42).Foo, (42).Foo) .
red pair((42).Nat, 7) .
red 0 .
red 00 .
red 1/2 .
red "s" .
"#;
        renders_as(
            src,
            &[
                "(42).Foo",
                "(-3).Foo",
                "pair((42).Foo, (42).Foo)",
                "pair((42).NzNat, 7)",
                "0",
                "00",
                "1/2",
                r#""s""#,
            ],
        );
        round_trips(src);
    }

    /// Kind-level terms that need a qualifier: `poly` range instances, a same-domain overload applied
    /// outside its declared domain, `~>` and explicit `[K]` ranges, a kind with two maximal sorts
    /// (`[Q,P]`), and a nested argument position.
    const KIND_QUALIFIED: &str = r#"fmod KIND-QUALIFIED is
  sorts Foo Foo2 Bar P Q R A B .
  subsort Foo < Foo2 .
  subsorts R < P Q .
  op a : -> Foo .
  op b : -> Foo2 .
  op g : Foo -> Universal [poly (0)] .
  op c : -> Universal [poly (0)] .
  op k : Foo -> A .
  op k : Foo -> B .
  op m : Foo ~> P .
  op m : Foo ~> Bar .
  op e : -> [A] .
  op e : -> [B] .
  op h : A -> A .
  op h : B -> B .
endfm
red (g(a)).Bar .
red (g(a)).Foo .
red (c).R .
red (k(b)).A .
red (k(b)).B .
red (m(a)).P .
red (e).B .
red h((e).A) .
"#;

    /// A qualified kind-level term names a user sort of its kind, never the `[K]` kind name the
    /// qualifier grammar lacks: its top symbol's declared non-error range, else the kind's first maximal
    /// sort. Every printed form reparses uniquely to the same term (`TNK-OUT-002`).
    #[test]
    fn kind_level_qualifiers_name_a_user_sort() {
        renders_as(
            KIND_QUALIFIED,
            &[
                "(g(a)).Bar",
                "(g(a)).Foo2",
                "(c).Q",
                "(k(b)).A",
                "(k(b)).B",
                "(m(a)).Q",
                "(e).B",
                "h((e).A)",
            ],
        );
        round_trips(KIND_QUALIFIED);
    }

    /// Overloaded `iter` operators. `Bar` and `Foo` are declared so that a bare `h(a)` first parses in
    /// the `Bar` kind, and `Foo` before `Bar` in the second module so that a bare `h(c)` first parses in
    /// the `Foo` kind.
    const ITER_OVERLOADS: &str = r#"fmod ITER-SAME-DOMAIN is
  sorts Bar Foo M N .
  op a : -> Foo .
  op h : Foo -> Bar .
  op h : Foo -> Foo [iter] .
  op f : Foo -> Foo .
  op o : -> M .
  op o : -> N .
  op p : M -> N .
  op p : N -> N [iter] .
endfm
red (h(a)).Foo .
red (h(a)).Bar .
red f((h(a)).Foo) .
red p((o).N) .
red p((o).M) .
fmod ITER-KINDS is
  sorts Foo Bar .
  op c : -> Foo .
  op c : -> Bar .
  op h : Foo -> Foo [iter] .
  op h : Bar -> Bar [iter] .
endfm
red h((c).Bar) .
red h((c).Foo) .
"#;

    /// A count-1 `iter` node prints as an ordinary application and is qualified like one: `(h(a)).Foo`
    /// when a same-domain overload shares the name, and its argument when the operator is ad-hoc
    /// overloaded and context does not fix the range. A range-fixing context keeps `h(a)` bare.
    #[test]
    fn count_one_iter_nodes_qualify_like_applications() {
        renders_as(
            ITER_OVERLOADS,
            &[
                "(h(a)).Foo",
                "(h(a)).Bar",
                "f(h(a))",
                "p((o).N)",
                "p((o).M)",
                "h((c).Bar)",
                "h((c).Foo)",
            ],
        );
        round_trips(ITER_OVERLOADS);
    }

    /// Two `iter` operators named `h` in different kinds beside a constant `c` of both kinds, and an
    /// `iter` operator `p` whose same-name overload is not `iter`.
    const ITER_POWERS: &str = r#"fmod ITER-POWERS is
  sorts Foo Bar M N .
  op c : -> Foo .
  op c : -> Bar .
  op h : Foo -> Foo [iter] .
  op h : Bar -> Bar [iter] .
  op g : Bar -> Bar .
  op o : -> M .
  op o : -> N .
  op p : M -> N .
  op p : N -> N [iter] .
endfm
red h(h((c).Bar)) .
red h^3((c).Foo) .
red g(h^2((c).Bar)) .
red p(p((o).N)) .
"#;

    /// `h^N(t)` parses as either `iter` operator named `h`, so its argument keeps a qualifier unless
    /// context fixes the range (`g(h^2(c))`). Only `p` has the `p^N` form, which fixes its argument.
    #[test]
    fn iter_power_arguments_qualify_when_iter_operators_share_a_name() {
        renders_as(
            ITER_POWERS,
            &["h^2((c).Bar)", "h^3((c).Foo)", "g(h^2(c))", "p^2(o)"],
        );
        round_trips(ITER_POWERS);
    }

    /// Kinds with two maximal sorts, printed `[B,A]` and `[List{Nat},Foo]` (`TNK-SORT-002`).
    const MULTI_SORT_KINDS: &str = r#"fmod MULTI-SORT-KINDS is
  sorts A B Sh Foo List{Nat} Sh2 .
  subsorts Sh < A B .
  subsorts Sh2 < Foo List{Nat} .
  op f : [A] -> [A] .
  op g : [Foo] -> [Foo] .
endfm
red f(X:[B,A]) .
red g(Y:[List{Nat},Foo]) .
red f(X:[Sh]) .
red g(Y:[Foo]) .
"#;

    /// A colon variable spelled with its kind's printed name, the form generated kind-level variables
    /// take (`#1:[B,A]`), parses as a variable at that kind's error sort, exactly as the single-sort
    /// spelling `X:[Sh]` does, and prints back unchanged.
    #[test]
    fn multi_sort_kind_colon_variables_parse() {
        renders_as(
            MULTI_SORT_KINDS,
            &[
                "f(X:[B,A])",
                "g(Y:[List{Nat},Foo])",
                "f(X:[Sh])",
                "g(Y:[Foo])",
            ],
        );
        let mut loaded = load_source(MULTI_SORT_KINDS).expect("load");
        let terms: Vec<(usize, Vec<crate::lex::Token>)> = loaded
            .commands
            .iter()
            .map(|(m, c)| match c {
                Command::Reduce { term, .. } => (*m, term.clone()),
                _ => panic!("fixture uses only reduce"),
            })
            .collect();
        let variable_sorts: Vec<_> = terms
            .iter()
            .map(|(m, term)| {
                let parsed =
                    parse_command_term(&loaded.modules[*m], &loaded.interner, term).expect("parse");
                let (result, _) =
                    reduce_command(&mut loaded.modules[*m], &loaded.interner, &parsed)
                        .expect("reduce");
                // A reduce subject's variable is a fresh constant of the variable's sort.
                let engine = &loaded.modules[*m].built.engine;
                let variable = engine.node(result).children().next().expect("argument");
                let sort = engine.sort_of(variable);
                assert!(engine.sorts().sort(sort).is_error, "kind-level variable");
                sort
            })
            .collect();
        assert_eq!(variable_sorts[0], variable_sorts[2], "`[B,A]` is `[Sh]`");
        assert_eq!(
            variable_sorts[1], variable_sorts[3],
            "`[List{{Nat}},Foo]` is `[Foo]`"
        );
    }
    #[test]
    fn bool_results_render_expected_forms() {
        renders_as(
            file!("bool.maude"),
            &["tt", "ff", "tt", "0", "s_^2(0)", "0"],
        );
    }
    #[test]
    fn nat_results_render_expected_forms() {
        // ACU order places the nullary `x` before the unary numeral, yielding the residue `x + 5`.
        renders_as(
            file!("nat.maude"),
            &[
                "5", "4", "5", "12", "4", "3", "1", "1024", "6", "tt", "ff", "tt", "x + 5",
            ],
        );
    }
    #[test]
    fn int_results_render_expected_forms() {
        renders_as(
            file!("int.maude"),
            &[
                "-3", "3", "0", "-3", "-5", "-3", "3", "-6", "6", "-3", "-1", "tt", "ff",
            ],
        );
    }

    /// The colored interactive form contains ANSI escapes and strips to the uncolored form.
    #[test]
    fn colored_strips_to_plain() {
        let mut loaded = load_source(file!("nat.maude")).expect("load");
        let term = match &loaded.commands[0].1 {
            Command::Reduce { term, .. } => term.clone(),
            _ => unreachable!(),
        };
        let parsed =
            parse_command_term(&loaded.modules[0], &loaded.interner, &term).expect("parse");
        let (result, _) =
            reduce_command(&mut loaded.modules[0], &loaded.interner, &parsed).expect("reduce");
        let m = &loaded.modules[0].built;
        let colored = print_pretty(m, &loaded.interner, result, true);
        let plain = print_pretty(m, &loaded.interner, result, false);
        assert!(
            colored.contains('\x1b'),
            "colored output carries ANSI escapes"
        );
        assert_eq!(
            strip_ansi(&colored),
            plain,
            "stripping ANSI yields the plain rendering"
        );
        assert_eq!(plain, "5", "2 + 3 = 5");
    }

    /// Remove ANSI SGR escape sequences (`ESC [ … m`).
    fn strip_ansi(s: &str) -> String {
        let mut out = String::new();
        let mut chars = s.chars();
        while let Some(c) = chars.next() {
            if c == '\x1b' {
                for d in chars.by_ref() {
                    if d == 'm' {
                        break;
                    }
                }
            } else {
                out.push(c);
            }
        }
        out
    }

    /// The `Term` printer uses the DAG printer's mixfix layout for patterns containing variables and
    /// prefix or mixfix operators. Trace rendering uses this path for `eq lhs = rhs .`.
    #[test]
    fn term_printer_renders_patterns() {
        let loaded = load_source(
            "fmod M is sort N . op 0 : -> N [ctor] . op s : N -> N [ctor] . \
             op add : N N -> N . op _+_ : N N -> N [assoc] . endfm",
        )
        .expect("load");
        let m = &loaded.modules[0].built;
        let i = &loaded.interner;
        let nat = m.sorts["N"];
        let s = m.ops[&("s".to_string(), 1)];
        let add = m.ops[&("add".to_string(), 2)];
        let plus = m.ops[&("_+_".to_string(), 2)];
        let v = |idx| Term::var(idx, nat);
        let names = ["X".to_string(), "Y".to_string(), "Z".to_string()];

        // prefix ops + variables: add(s(X), Y)
        let t1 = Term::op(add, vec![Term::op(s, vec![v(0)]), v(1)]);
        assert_eq!(print_term(m, i, &t1, &names, false), "add(s(X), Y)");
        // right-associating infix, nested binary `+(X, +(Y, Z))` renders flat `X + Y + Z`
        let t2 = Term::op(plus, vec![v(0), Term::op(plus, vec![v(1), v(2)])]);
        assert_eq!(print_term(m, i, &t2, &names, false), "X + Y + Z");
        // a constant
        assert_eq!(
            print_term(
                m,
                i,
                &Term::constant(m.ops[&("0".to_string(), 0)]),
                &[],
                false
            ),
            "0"
        );
    }
}
