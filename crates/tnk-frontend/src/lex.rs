//! Tokenization and operator-name splitting.
//!
//! Tokens are separated by whitespace and by the **special-splitting** punctuation `( ) [ ] { } ,`
//! (each its own token); all other characters can form an identifier token. The statement or command
//! terminator `.` is a `.` followed by whitespace, EOF, punctuation, or a top-level keyword, and is
//! distinguished from a `.` inside a float, structured sort, or operator. Strings are `"…"`,
//! quoted identifiers start with `'`, and a backquote escapes a splitting character into an identifier.
//!
//! Line comments (`***`/`---` to end of line) and **bracketed** comments (`***( … )` / `---( … )`, balanced
//! parentheses across newlines) are both handled. Tokens are interned ([`Interner`]), making equality a
//! `u32` comparison. Bubble collection is an explicit surface-parser operation rather than lexer state.

use std::collections::HashMap;

/// An interned token string (an index into the [`Interner`]).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Sym(u32);

/// String interner: text ↔ [`Sym`]. Token equality is `Sym` equality.
#[derive(Debug, Default, Clone)]
pub struct Interner {
    strings: Vec<String>,
    lookup: HashMap<String, Sym>,
}

impl Interner {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn intern(&mut self, s: &str) -> Sym {
        if let Some(&sym) = self.lookup.get(s) {
            return sym;
        }
        let sym = Sym(u32::try_from(self.strings.len()).expect("interner exceeded u32"));
        self.strings.push(s.to_string());
        self.lookup.insert(s.to_string(), sym);
        sym
    }
    pub fn resolve(&self, sym: Sym) -> &str {
        &self.strings[sym.0 as usize]
    }
    /// Resolve a raw token code stored by the kernel in a variable DAG node.
    pub fn resolve_index(&self, index: u32) -> &str {
        &self.strings[index as usize]
    }
    /// The [`Sym`] for an already-interned string, or `None`. Immutable lookup (no interning) — used by
    /// the surface parser (which holds `&Interner`) to obtain the mixfix fragment chars (`:`/`_`) it
    /// splices into synthesized `omod` attribute-operator names; [`tokenize`] guarantees they are interned.
    pub fn get(&self, s: &str) -> Option<Sym> {
        self.lookup.get(s).copied()
    }
}

impl Sym {
    /// Raw intern index assigned in first-occurrence order. It is also the name-order rank carried
    /// by command-subject pseudo-variables into the kernel.
    pub fn index(self) -> u32 {
        self.0
    }

    /// Rebuild a [`Sym`] from a raw intern index previously obtained via [`index`](Self::index) —
    /// the inverse used when a name code comes back out of a kernel `Var` leaf for printing. The
    /// caller must pass an index minted by the same [`Interner`].
    pub fn from_raw(raw: u32) -> Sym {
        Sym(raw)
    }
}

/// The lexical class of a [`Token`], computed at scan time from its text.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TokKind {
    /// An identifier / keyword / operator-name fragment (the default).
    Ident,
    /// A splitting punctuation character `( ) [ ] { } ,` (its own token).
    Punct,
    /// The statement/command terminator `.` (a `.` followed by whitespace/EOF/punctuation).
    Dot,
    /// A natural-number literal `0 | [1-9][0-9]*`.
    Number,
    /// A string literal `"…"` whose unescaped closing quote is the token's final character. A string
    /// glued into a longer identifier (`"x"y`, `foo"bar"`) is an `Ident`, not a `Str`.
    Str,
    /// A float literal accepted by `is_float_literal`: `1.5`, `-1.5`, `5.0e-1`, and the abbreviated
    /// forms `1.`, `.5`, `1.e3`, `.5e2`, `1e3`, and `Infinity`.
    Float,
    /// A negative integer `-[0-9]+` with nonzero magnitude. The minus sign must be glued to the
    /// digits. Float recognition takes precedence; a spaced `-` remains a separate token.
    NegNumber,
    /// A quoted identifier `'…`.
    Qid,
    /// A glued rational literal `[-]num/den`, recognized by `is_rational_literal`. A spaced
    /// `1 / 6` remains three tokens and is parsed as binary division.
    Rational,
    /// An iteration-symbol token `f^count`, recognized by `is_iter_token`, such as `s_^10`. The text
    /// before the final `^` is the operator name; the trailing nonzero-leading digits are the count.
    Iter,
}

/// A lexical token: its interned text, source line, and class.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Token {
    pub sym: Sym,
    pub line: u32,
    pub kind: TokKind,
}

impl Token {
    /// The token's text.
    pub fn text<'a>(&self, i: &'a Interner) -> &'a str {
        i.resolve(self.sym)
    }
}

/// A splitting punctuation character (its own token; not part of an identifier).
pub(crate) fn is_punct(c: char) -> bool {
    matches!(c, '(' | ')' | '[' | ']' | '{' | '}' | ',')
}

/// Whether the identifier built so far is a colon-variable prefix `name:base`. `base` may still be empty
/// while scanning the opening `[` of a kind-qualified variable (`A:[Maybe{Oid}]`). Quoted identifiers
/// are operator names, never variables; punctuation following one must remain syntax.
fn colon_var_shape(text: &str) -> bool {
    matches!(
        text.rsplit_once(':'),
        Some((name, _base)) if !name.is_empty() && !name.starts_with('\'')
    )
}

/// A line comment `***`/`---` begins at `chars[j]`.
fn is_line_comment_start(chars: &[char], j: usize) -> bool {
    matches!(chars.get(j), Some('*') | Some('-'))
        && chars.get(j + 1) == chars.get(j)
        && chars.get(j + 2) == chars.get(j)
}

/// A top-level keyword that can follow a same-line terminating dot.
fn is_top_level_keyword(w: &str) -> bool {
    matches!(
        w,
        "fmod"
            | "mod"
            | "fth"
            | "th"
            | "endfm"
            | "endm"
            | "endfth"
            | "endth"
            | "view"
            | "endv"
            | "sort"
            | "sorts"
            | "subsort"
            | "subsorts"
            | "op"
            | "ops"
            | "var"
            | "vars"
            | "protecting"
            | "pr"
            | "extending"
            | "ex"
            | "including"
            | "inc"
            | "eq"
            | "ceq"
            | "mb"
            | "cmb"
            | "rl"
            | "crl"
            | "red"
            | "reduce"
            | "check"
            | "match"
            | "xmatch"
            | "rew"
            | "rewrite"
            | "search"
            | "smt-search"
    )
}

/// Whether `chars[i] == '.'` is a statement/command **terminator** rather than an ordinary token (a `.`
/// inside a float `1.5`, a structured sort, or the `_._` operator).
///
/// A dot terminates when the next nonblank input is a newline, EOF, line comment, or top-level keyword.
/// Before any ordinary token on the same line, it remains the `_._` operator.
fn is_terminator_dot(chars: &[char], i: usize) -> bool {
    let mut j = i + 1;
    while matches!(chars.get(j), Some(' ') | Some('\t') | Some('\r')) {
        j += 1;
    }
    match chars.get(j) {
        None | Some('\n') => return true,
        _ if is_line_comment_start(chars, j) => return true,
        _ => {}
    }
    // Read the next word and check it against the top-level keywords.
    let start = j;
    while let Some(&c) = chars.get(j) {
        if c.is_whitespace() || is_punct(c) {
            break;
        }
        j += 1;
    }
    let word: String = chars[start..j].iter().collect();
    is_top_level_keyword(&word)
}

/// A token is a string literal only when it starts with `"` and its matching unescaped close quote is
/// the final character. A token containing a shorter quoted segment (`"x"y`, `foo"bar"`) is an
/// identifier. ASCII quote and backslash bytes make byte scanning safe across multibyte content.
fn is_string_literal(text: &str) -> bool {
    let bytes = text.as_bytes();
    if bytes.first() != Some(&b'"') {
        return false;
    }
    let mut seen_backslash = false;
    for (idx, &c) in bytes.iter().enumerate().skip(1) {
        match c {
            b'\\' => seen_backslash = !seen_backslash,
            b'"' if !seen_backslash => return idx == bytes.len() - 1,
            _ => seen_backslash = false,
        }
    }
    false // unterminated
}

/// Classify scanned identifier text in precedence order: quoted identifier/string, iteration, float,
/// integer, rational, then ordinary identifier.
pub(crate) fn classify(text: &str) -> TokKind {
    if is_string_literal(text) {
        return TokKind::Str;
    }
    if text.starts_with('\'') {
        return TokKind::Qid;
    }
    if is_iter_token(text) {
        return TokKind::Iter;
    }
    if !text.is_empty() && text.bytes().all(|b| b.is_ascii_digit()) {
        return TokKind::Number;
    }
    if is_float_literal(text) {
        return TokKind::Float;
    }
    if is_neg_integer(text) {
        return TokKind::NegNumber;
    }
    if is_rational_literal(text) {
        return TokKind::Rational;
    }
    TokKind::Ident
}

/// A glued rational literal has an optional `-`, a decimal numerator, `/`, and a positive decimal
/// denominator without a leading zero. Zero numerators must be exactly unsigned `0`. Examples:
/// `1/6`, `2/4`, `-7/3`, `0/5`; rejected: `1/0`, `1/06`, `-0/3`, `00/3`, `1/6/7`.
fn is_rational_literal(text: &str) -> bool {
    let (neg, rest) = match text.strip_prefix('-') {
        Some(r) => (true, r),
        None => (false, text),
    };
    let Some((num, den)) = rest.split_once('/') else {
        return false;
    };
    // Numerator: all digits, non-empty; a `0` numerator is allowed only unsigned and only as exactly `0`.
    if num.is_empty() || !num.bytes().all(|b| b.is_ascii_digit()) {
        return false;
    }
    if num.bytes().next() == Some(b'0') && (neg || num.len() != 1) {
        return false;
    }
    // Denominator: all digits, non-empty, with a nonzero leading digit (>= 1, no leading zero) and no
    // further `/`.
    !den.is_empty() && den.bytes().all(|b| b.is_ascii_digit()) && den.as_bytes()[0] != b'0'
}

/// An iteration token `f^count` has a non-empty operator prefix, `^`, and a maximal trailing decimal
/// count beginning with a nonzero digit. The prefix may contain `_`; the count may exceed `u64`.
fn is_iter_token(text: &str) -> bool {
    let Some((prefix, digits)) = text.rsplit_once('^') else {
        return false;
    };
    !prefix.is_empty()
        && !digits.is_empty()
        && digits.bytes().all(|b| b.is_ascii_digit())
        && digits.as_bytes()[0] != b'0'
}

/// A negative-integer literal is `-` glued to decimal digits with nonzero magnitude. Floats are
/// classified first; `-0` and `-00` are excluded because zero has its own token class.
fn is_neg_integer(text: &str) -> bool {
    let Some(digits) = text.strip_prefix('-') else {
        return false;
    };
    !digits.is_empty()
        && digits.bytes().all(|b| b.is_ascii_digit())
        && digits.bytes().any(|b| b != b'0')
}

/// A float literal has an optional sign followed by `Infinity` or a mantissa/exponent containing at
/// least one digit and either a decimal point or `[eE]` exponent. Accepted forms include `1.5`,
/// `-1.5`, `5.0e-1`, `1.`, `.5`, `1.e3`, `.5e2`, and `1e3`. A dangling exponent, lone point, or bare
/// integer is not a float. Only a sign attached to the number is part of the token.
fn is_float_literal(text: &str) -> bool {
    let t = text.strip_prefix(['+', '-']).unwrap_or(text);
    if t == "Infinity" {
        return true;
    }
    let (mantissa, exponent) = match t.split_once(['e', 'E']) {
        Some((m, e)) => (m, Some(e)),
        None => (t, None),
    };
    let (int_part, frac_part) = match mantissa.split_once('.') {
        Some((i, f)) => (i, Some(f)),
        None => (mantissa, None),
    };
    let all_digits = |p: &str| p.bytes().all(|b| b.is_ascii_digit());
    if !all_digits(int_part) || !frac_part.is_none_or(all_digits) {
        return false;
    }
    // At least one digit somewhere in the mantissa…
    if int_part.is_empty() && frac_part.is_none_or(str::is_empty) {
        return false;
    }
    // …and a `.` or an exponent to make it a float rather than an integer numeral. A present exponent
    // must itself carry digits (a dangling `1.5e` is not a float).
    match exponent {
        Some(e) => {
            let e = e.strip_prefix(['+', '-']).unwrap_or(e);
            !e.is_empty() && all_digits(e)
        }
        None => frac_part.is_some(),
    }
}

/// Tokenize module source into a [`Token`] stream, interning token text into `interner`. Handles
/// whitespace, `***`/`---` comments, splitting punctuation, string literals, the terminator `.`, and
/// identifier backquote escapes.
pub fn tokenize(src: &str, interner: &mut Interner) -> Vec<Token> {
    // Guarantee the two mixfix fragment chars the `omod` class desugaring splices into synthesized
    // attribute names are interned. The surface parser only holds `&Interner`.
    interner.intern(":");
    interner.intern("_");

    let chars: Vec<char> = src.chars().collect();
    let n = chars.len();
    let mut i = 0;
    let mut line = 1u32;
    let mut out = Vec::new();

    while i < n {
        let c = chars[i];
        if c == '\n' {
            line += 1;
            i += 1;
            continue;
        }
        if c.is_whitespace() {
            i += 1;
            continue;
        }
        // `***` / `---` comments are bracketed across lines when the first nonblank character after
        // the marker is `(`; parentheses balance, and backquoted parentheses do not count. Otherwise
        // the comment ends with the line. Echo forms beginning `***>` or `--->` are line comments.
        let is_comment =
            |k: char| chars[i] == k && chars.get(i + 1) == Some(&k) && chars.get(i + 2) == Some(&k);
        if is_comment('*') || is_comment('-') {
            i += 3;
            let mut j = i;
            while matches!(chars.get(j), Some(' ') | Some('\t') | Some('\r')) {
                j += 1;
            }
            if chars.get(j) == Some(&'(') {
                i = j;
                let (mut depth, mut bq) = (0u32, false);
                while i < n {
                    let ch = chars[i];
                    if ch == '\n' {
                        line += 1;
                    }
                    if !bq && ch == '(' {
                        depth += 1;
                    } else if !bq && ch == ')' {
                        depth -= 1;
                        if depth == 0 {
                            i += 1;
                            break;
                        }
                    }
                    bq = !bq && ch == '`';
                    i += 1;
                }
            } else {
                while i < n && chars[i] != '\n' {
                    i += 1;
                }
            }
            continue;
        }
        if is_punct(c) {
            let sym = interner.intern(&c.to_string());
            out.push(Token {
                sym,
                line,
                kind: TokKind::Punct,
            });
            i += 1;
            continue;
        }
        if c == '.' && is_terminator_dot(&chars, i) {
            let sym = interner.intern(".");
            out.push(Token {
                sym,
                line,
                kind: TokKind::Dot,
            });
            i += 1;
            continue;
        }
        // Scan an identifier token until whitespace, punctuation, or a terminating dot. Quoted string
        // syntax can remain embedded, so `foo"bar"` and `"x"y` each stay one identifier; a lone quoted
        // token classifies as a string.
        let mut text = String::new();
        while i < n {
            let ch = chars[i];
            // Consume a complete quoted segment and keep scanning so it can remain embedded in the
            // surrounding identifier (`a"b"c` and `"x"y` are each one token).
            if ch == '"' {
                text.push(ch);
                i += 1;
                while i < n && chars[i] != '"' {
                    if chars[i] == '\\' && i + 1 < n {
                        text.push(chars[i]);
                        text.push(chars[i + 1]);
                        i += 2;
                    } else {
                        if chars[i] == '\n' {
                            line += 1;
                        }
                        text.push(chars[i]);
                        i += 1;
                    }
                }
                if i < n {
                    text.push(chars[i]); // closing quote
                    i += 1;
                }
                continue;
            }
            // A colon glued on only one side is syntax punctuation, not a colon-variable token:
            // object syntax writes both `:Snd` and `buff:` without spaces. Preserve `X:Sort` as one
            // token, but emit a leading/trailing maximal colon run separately.
            if ch == ':' {
                // `:=` is a reserved statement/strategy connective. The one-sided object-colon
                // split below must not turn it into the two tokens `:` and `=`.
                if chars.get(i + 1) == Some(&'=') {
                    if text.is_empty() {
                        text.push_str(":=");
                        i += 2;
                    }
                    break;
                }
                if text.is_empty() {
                    while i < n && chars[i] == ':' {
                        text.push(':');
                        i += 1;
                    }
                    break;
                }
                // A kind-qualified variable starts `A:[…]`; unlike an ordinary punctuation boundary,
                // this colon belongs to the variable token so the balanced-bracket branch below can
                // consume the whole kind name.
                if chars.get(i + 1) == Some(&'[') && !text.starts_with('\'') {
                    text.push(':');
                    i += 1;
                    continue;
                }
                let next_is_boundary = chars
                    .get(i + 1)
                    .is_none_or(|next| next.is_whitespace() || is_punct(*next));
                if next_is_boundary {
                    if text == "id" {
                        text.push(':');
                        i += 1;
                        continue;
                    }
                    break;
                }
            }
            // A structured-sort colon variable keeps its braces in one token: `L:List{Nat}` (and the chained
            // `X:Box{ToT2}{C2}`) — consume the balanced `{ … }` group rather than letting `{` split it off.
            if ch == '{' && colon_var_shape(&text) {
                let mut depth = 0u32;
                while i < n {
                    let cj = chars[i];
                    if cj == '\n' {
                        line += 1;
                    }
                    text.push(cj);
                    i += 1;
                    match cj {
                        '{' => depth += 1,
                        '}' => {
                            depth -= 1;
                            if depth == 0 {
                                break;
                            }
                        }
                        _ => {}
                    }
                }
                continue;
            }
            // A colon variable may name its connected-component kind directly: `A:[Maybe{Oid}]`.
            // Only a bracket immediately after the colon belongs to that variable. In
            // `Q:Qid[TL:NeTermList]`, `Q:Qid` is complete and `[` starts the meta-term application.
            // Keep the direct kind's balanced brackets (and structured sorts inside them) in one token;
            // whitespace inside a kind name is presentation only.
            if ch == '[' && text.ends_with(':') {
                let mut depth = 0u32;
                while i < n {
                    let cj = chars[i];
                    if cj == '\n' {
                        line += 1;
                    }
                    if !cj.is_whitespace() {
                        text.push(cj);
                    }
                    i += 1;
                    match cj {
                        '[' => depth += 1,
                        ']' => {
                            depth -= 1;
                            if depth == 0 {
                                break;
                            }
                        }
                        _ => {}
                    }
                }
                continue;
            }
            if ch.is_whitespace() || is_punct(ch) {
                break;
            }
            if ch == '.' && is_terminator_dot(&chars, i) {
                break;
            }
            if ch == '`' && i + 1 < n {
                let next = chars[i + 1];
                // Backquote escapes split characters into this token. The object-attribute suffix
                // `` `:_ `` retains the backquote in its reflected operator identifier.
                if next == '_' || next == ':' || is_punct(next) {
                    if text.starts_with('\'')
                        && next == ':'
                        && chars.get(i + 2).is_some_and(|following| *following == '_')
                    {
                        text.push('`');
                    }
                    text.push(next);
                    i += 2;
                    continue;
                }
                // Before a normal character, backquote denotes an inter-token blank. A quoted
                // identifier retains it as content; a bare identifier ends here, making
                // `` hello`world `` tokenize like `hello world`.
                if text.starts_with('\'') {
                    text.push('`');
                    text.push(next);
                    i += 2;
                    continue;
                }
                i += 1; // consume the separating blank
                if text.is_empty() {
                    continue; // a leading blank: nothing to emit yet, keep scanning
                }
                break; // emit the token so far; the next token starts at `next`
            }
            text.push(ch);
            i += 1;
        }
        let kind = classify(&text);
        let sym = interner.intern(&text);
        out.push(Token { sym, line, kind });
    }
    out
}

/// A fragment of an operator's mixfix syntax: a literal name fragment, or an argument hole (`_`).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Frag {
    /// A literal name fragment (interned).
    Tok(Sym),
    /// An argument position (`_`).
    Hole,
}

/// Split an operator name's text into mixfix fragments at `_`: `_+_` → `[Hole, +, Hole]`; `s_` →
/// `[s, Hole]`; `if_then_else_fi` → `[if, Hole, then, Hole, else, Hole, fi]`; a bare `gcd` → `[gcd]`
/// (prefix-only). Names split by punctuation, such as `<_,_>`, are reassembled by the surface parser
/// from these per-token fragments.
pub fn split_mixfix(name: &str, interner: &mut Interner) -> Vec<Frag> {
    let mut frags = Vec::new();
    let mut pending = String::new();
    let mut chars = name.chars().peekable();
    while let Some(ch) = chars.next() {
        // Backquote escapes split characters into the current fragment. Before a normal character it
        // separates operator-name fragments.
        if ch == '`' {
            match chars.peek() {
                Some(&next) if next == '_' || is_punct(next) => {
                    chars.next();
                    pending.push(next);
                }
                _ => {
                    if !pending.is_empty() {
                        frags.push(Frag::Tok(interner.intern(&pending)));
                        pending.clear();
                    }
                }
            }
            continue;
        }
        // A hole (`_`) or a punctuation char (`( ) [ ] { } ,`) ends the pending literal and becomes its
        // own fragment. Splitting on punctuation — like the main lexer — is what makes an op name whose
        // tokens glue punctuation to text (`_=[_]_` → `= [ ]`) align with how a *term* tokenizes (`=[Z]`
        // lexes as `= [ Z ]`); without it the grammar terminal `=[` could never match.
        //
        // `:` splits too — but unlike punctuation it is *not* split by the main lexer (so `X:Nat` stays
        // one colon-variable token). The asymmetry is deliberate: an op name's `:` is a syntactic
        // separator that is always written space-delimited (`bal :_`, `<_:_|_>`), so in a *term* it is
        // its own token (`bal : n0` → `bal`, `:`, `n0` — `bal:n0` with no space would be a variable).
        // The name's tokens, however, get concatenated into the canonical string (`[bal][:_]` → `bal:_`),
        // gluing `:` to `bal`; splitting it back out makes the grammar terminal `:` match the term's
        // standalone colon in object/message attribute operators such as `bal :_` and `turns :_`.
        // The lexer reserves `:=` as one token (matching conditions, strategy definitions, and ordinary
        // user mixfix operators such as assignment). Keep the operator grammar on the same tokenization;
        // the generic colon branch below would otherwise split `_:=_` into the unmatchable `:` + `=`.
        if ch == ':' && chars.peek() == Some(&'=') {
            if !pending.is_empty() {
                frags.push(Frag::Tok(interner.intern(&pending)));
                pending.clear();
            }
            chars.next();
            frags.push(Frag::Tok(interner.intern(":=")));
            continue;
        }

        if ch == '_' || ch == ':' || is_punct(ch) {
            if !pending.is_empty() {
                frags.push(Frag::Tok(interner.intern(&pending)));
                pending.clear();
            }
            if ch == '_' {
                frags.push(Frag::Hole);
            } else if ch == ':' {
                // A maximal run of `:` is one identifier token in the main lexer (`::` in `X :: Y`).
                // It must therefore remain one fragment here: per-character fragments could neither
                // match a term's single `::` token nor print without an inner space.
                let mut run = String::from(":");
                while chars.peek() == Some(&':') {
                    chars.next();
                    run.push(':');
                }
                frags.push(Frag::Tok(interner.intern(&run)));
            } else {
                frags.push(Frag::Tok(interner.intern(ch.encode_utf8(&mut [0u8; 4]))));
            }
        } else {
            pending.push(ch);
        }
    }
    if !pending.is_empty() {
        frags.push(Frag::Tok(interner.intern(&pending)));
    }
    frags
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Decode a token stream to `(text, kind)` pairs for assertions.
    fn lex(src: &str) -> (Interner, Vec<(String, TokKind)>) {
        let mut i = Interner::new();
        let toks = tokenize(src, &mut i);
        let decoded = toks
            .iter()
            .map(|t| (t.text(&i).to_string(), t.kind))
            .collect();
        (i, decoded)
    }

    #[test]
    fn splits_on_whitespace_and_punctuation() {
        let (_i, t) = lex("op _+_ : Nat Nat -> Nat .");
        let texts: Vec<&str> = t.iter().map(|(s, _)| s.as_str()).collect();
        assert_eq!(texts, ["op", "_+_", ":", "Nat", "Nat", "->", "Nat", "."]);
        assert_eq!(
            t.last().unwrap().1,
            TokKind::Dot,
            "trailing . is the terminator"
        );
    }

    #[test]
    fn keeps_matching_and_strategy_definition_connective() {
        let (_i, t) = lex("ceq pred(N) = M if s M := N . sd go:= r1 .");
        let texts: Vec<&str> = t.iter().map(|(s, _)| s.as_str()).collect();
        assert_eq!(
            texts,
            [
                "ceq", "pred", "(", "N", ")", "=", "M", "if", "s", "M", ":=", "N", ".", "sd", "go",
                ":=", "r1", ".",
            ]
        );
    }

    #[test]
    fn splits_one_sided_object_colons_but_keeps_colon_variables() {
        let (_i, t) = lex("< O :Snd | buff: L > X:Sort X::Y ::");
        let texts: Vec<&str> = t.iter().map(|(s, _)| s.as_str()).collect();
        assert_eq!(
            texts,
            [
                "<", "O", ":", "Snd", "|", "buff", ":", "L", ">", "X:Sort", "X::Y", "::"
            ]
        );
    }

    /// A structured-sort colon variable keeps its braces in one token (`L:List{Nat}`, and the chained
    /// `X:Box{A}{B}`), so it matches the `ColonVar` grammar terminal — but a *plain* structured sort
    /// (`List{Nat}`, no colon) still splits on the braces. `N:Nat` is one token.
    #[test]
    fn structured_colon_variable_is_one_token() {
        let (_i, t) = lex("hd(c(N:Nat, L:List{Nat}), X:Box{A}{B}) List{Nat}");
        let texts: Vec<&str> = t.iter().map(|(s, _)| s.as_str()).collect();
        assert_eq!(
            texts,
            [
                "hd",
                "(",
                "c",
                "(",
                "N:Nat",
                ",",
                "L:List{Nat}",
                ")",
                ",",
                "X:Box{A}{B}",
                ")",
                // a plain structured sort (no colon) is unaffected — still `List { Nat }`.
                "List",
                "{",
                "Nat",
                "}",
            ]
        );
        assert_eq!(
            t[6].1,
            TokKind::Ident,
            "the colon-var token classifies as an identifier"
        );
    }

    /// A bracketed `***( … )` or `---( … )` comment spans balanced parentheses across lines;
    /// backquoted parentheses do not count. Plain `***` and `---` comments end at the newline.
    #[test]
    fn bracketed_and_line_comments() {
        let texts = |s| {
            let (_i, t) = lex(s);
            t.into_iter().map(|(x, _)| x).collect::<Vec<_>>()
        };
        assert_eq!(texts("a\n***( c1\nc2 )\nb"), ["a", "b"]); // multi-line bracketed
        assert_eq!(texts("a ***(x) b"), ["a", "b"]); // `***(` with no space
        assert_eq!(texts("a *** line ( unbalanced\nb"), ["a", "b"]); // line comment: `(` ignored
        assert_eq!(texts("a ***( p `) q ) b"), ["a", "b"]); // a backquoted `)` does not close early
        assert_eq!(texts("a ---> echo ( x\nb"), ["a", "b"]); // `--->` echo form is a line comment
    }

    #[test]
    fn prefix_application_punctuation() {
        let (_i, t) = lex("gcd(12, 18)");
        let texts: Vec<&str> = t.iter().map(|(s, _)| s.as_str()).collect();
        assert_eq!(texts, ["gcd", "(", "12", ",", "18", ")"]);
        assert_eq!(t[2].1, TokKind::Number); // 12
    }

    #[test]
    fn classifies_literals() {
        let (_i, t) = lex(r#"0 42 1.5 "abc" 'foo s_"#);
        let kinds: Vec<TokKind> = t.iter().map(|(_, k)| *k).collect();
        use TokKind::*;
        assert_eq!(kinds, [Number, Number, Float, Str, Qid, Ident]);
        assert_eq!(t[3].0, "\"abc\"", "the string keeps its quotes");
    }

    #[test]
    fn quoted_identifier_preserves_split_character_escapes() {
        let (_i, tokens) = lex("'first`:_ 'X:Foo");
        assert_eq!(
            tokens,
            [
                ("'first`:_".to_string(), TokKind::Qid),
                ("'X:Foo".to_string(), TokKind::Qid),
            ]
        );
    }

    /// A quoted string segment can occur inside one identifier token: `a"b"c`, `foo"bar"`, and
    /// `"x"y` are identifiers, while a bare complete string is a `Str` constant. Strings separated
    /// by whitespace or punctuation remain separate tokens.
    #[test]
    fn string_glued_into_identifier() {
        use TokKind::*;
        let t = |s| lex(s).1;
        // A token that is exactly one string is `Str` (close-quote is the last char).
        assert_eq!(t(r#""hello""#), [("\"hello\"".into(), Str)]);
        assert_eq!(
            t(r#""""#),
            [("\"\"".into(), Str)],
            "the empty string is a Str"
        );
        // A string segment glued to other text produces one `Ident` token.
        assert_eq!(t(r#"a"b"c"#), [("a\"b\"c".into(), Ident)]);
        assert_eq!(t(r#"foo"bar""#), [("foo\"bar\"".into(), Ident)]);
        assert_eq!(
            t(r#""x"y"#),
            [("\"x\"y".into(), Ident)],
            "leading string + glued suffix = Ident"
        );
        // An escaped quote inside the string does not end it; the trailing `"` does.
        assert_eq!(t(r#""a\"b""#), [("\"a\\\"b\"".into(), Str)]);
        // Bare strings separated by whitespace or punctuation remain separate tokens.
        assert_eq!(
            t(r#"len("hello")"#),
            [
                ("len".into(), Ident),
                ("(".into(), Punct),
                ("\"hello\"".into(), Str),
                (")".into(), Punct),
            ]
        );
        // In `"ab" . "cd"`, the middle `.` is followed by another token rather than a top-level keyword,
        // so it remains the `_._` string-concatenation operator instead of terminating the command.
        assert_eq!(
            t(r#""ab" . "cd""#),
            [
                ("\"ab\"".into(), Str),
                (".".into(), Ident),
                ("\"cd\"".into(), Str),
            ]
        );
    }

    /// `classify` leaves every all-digit run in the broad `Number` class. Grammar matching then rejects
    /// all-zero multi-digit spellings while accepting leading-zero positive numerals and normalizing
    /// their value.
    #[test]
    fn leading_zero_numerals_stay_number() {
        use TokKind::*;
        assert_eq!(classify("0"), Number, "the bare zero constant");
        assert_eq!(
            classify("00"),
            Number,
            "all-zero run: Number here; rejected at the grammar terminal"
        );
        assert_eq!(classify("000"), Number);
        assert_eq!(
            classify("01"),
            Number,
            "leading-zero numeral: Number, becomes `1` (zeros stripped)"
        );
        assert_eq!(classify("007"), Number);
        assert_eq!(classify("123"), Number);
        // A glued negative zero is not a numeral and therefore remains an identifier.
        assert_eq!(classify("-0"), Ident);
    }

    #[test]
    fn dot_inside_float_is_not_a_terminator() {
        let (_i, t) = lex("red 1.5 .");
        let texts: Vec<&str> = t.iter().map(|(s, _)| s.as_str()).collect();
        assert_eq!(texts, ["red", "1.5", "."]);
        assert_eq!(t[1].1, TokKind::Float);
        assert_eq!(t[2].1, TokKind::Dot);
    }

    /// A glued sign belongs to its literal token; a spaced sign remains an operator. This keeps binary
    /// subtraction distinct while recognizing signed floats and negative integers.
    #[test]
    fn signed_and_exponent_floats() {
        assert_eq!(classify("-1.5"), TokKind::Float);
        assert_eq!(classify("+0.25"), TokKind::Float);
        assert_eq!(classify("5.0e-1"), TokKind::Float);
        assert_eq!(classify("2.0E+3"), TokKind::Float);
        assert_eq!(classify("4.0"), TokKind::Float);
        // A dotless `-N` is a negative-integer literal rather than a float.
        assert_eq!(
            classify("-3"),
            TokKind::NegNumber,
            "`-3` is a SMALL_NEG, parsed via the `-_` op"
        );
        assert_eq!(classify("-7"), TokKind::NegNumber);
        assert_eq!(
            classify("-0"),
            TokKind::Ident,
            "`-0` (magnitude zero) is not SMALL_NEG"
        );
        // Abbreviated float forms and their canonical values: `1.` → `1.0`, `.5` → `5.0e-1`,
        // `1.e3`/`1e3` → `1.0e+3`, `.5e2` → `5.0e+1`; `Infinity` remains infinite.
        assert_eq!(classify("1."), TokKind::Float);
        assert_eq!(classify(".5"), TokKind::Float);
        assert_eq!(classify("1.e3"), TokKind::Float);
        assert_eq!(classify(".5e2"), TokKind::Float);
        assert_eq!(classify("1e3"), TokKind::Float);
        assert_eq!(classify("Infinity"), TokKind::Float);
        assert_eq!(classify("-Infinity"), TokKind::Float, "signed Infinity");
        // A dangling exponent and a lone point remain identifiers.
        assert_eq!(
            classify("1.5e"),
            TokKind::Ident,
            "a dangling exponent is not a float"
        );
        assert_eq!(classify("."), TokKind::Ident, "a lone dot is not a float");
        assert_eq!(
            classify("5"),
            TokKind::Number,
            "a bare integer numeral is a Number, not a Float"
        );
        // `5.0 - 1.5` keeps the spaced `-` as a separate Ident token (binary minus).
        let (_i, t) = lex("5.0 - 1.5");
        let decoded: Vec<(&str, TokKind)> = t.iter().map(|(s, k)| (s.as_str(), *k)).collect();
        assert_eq!(
            decoded,
            [
                ("5.0", TokKind::Float),
                ("-", TokKind::Ident),
                ("1.5", TokKind::Float)
            ]
        );
        // A glued `-7` is one `NegNumber`; spaced subtraction keeps `-` separate. Consequently
        // `5 -7` tokenizes as `5`, `-7` and does not parse as subtraction.
        let toks = |s| lex(s).1;
        assert_eq!(
            toks("-7 quo 2"),
            [
                ("-7".into(), TokKind::NegNumber),
                ("quo".into(), TokKind::Ident),
                ("2".into(), TokKind::Number)
            ]
        );
        assert_eq!(
            toks("5 -7"),
            [
                ("5".into(), TokKind::Number),
                ("-7".into(), TokKind::NegNumber)
            ]
        );
        assert_eq!(
            toks("5 - 7"),
            [
                ("5".into(), TokKind::Number),
                ("-".into(), TokKind::Ident),
                ("7".into(), TokKind::Number)
            ]
        );
    }

    #[test]
    fn comments_skipped_and_lines_tracked() {
        let mut i = Interner::new();
        let toks = tokenize("a *** comment\nb --- another\nc", &mut i);
        let texts: Vec<&str> = toks.iter().map(|t| t.text(&i)).collect();
        assert_eq!(texts, ["a", "b", "c"]);
        assert_eq!((toks[0].line, toks[1].line, toks[2].line), (1, 2, 3));
    }

    #[test]
    fn op_name_splitting() {
        let mut i = Interner::new();
        let frag = |name: &str, i: &mut Interner| {
            split_mixfix(name, i)
                .iter()
                .map(|f| match f {
                    Frag::Hole => "_".to_string(),
                    Frag::Tok(s) => i.resolve(*s).to_string(),
                })
                .collect::<Vec<_>>()
        };
        assert_eq!(frag("_+_", &mut i), ["_", "+", "_"]);
        assert_eq!(frag("s_", &mut i), ["s", "_"]);
        assert_eq!(frag("-_", &mut i), ["-", "_"]);
        assert_eq!(frag("_<=_", &mut i), ["_", "<=", "_"]);
        assert_eq!(frag("_:=_", &mut i), ["_", ":=", "_"]);
        assert_eq!(
            frag("if_then_else_fi", &mut i),
            ["if", "_", "then", "_", "else", "_", "fi"]
        );
        assert_eq!(
            frag("gcd", &mut i),
            ["gcd"],
            "a bare identifier is prefix-only"
        );
    }
}
