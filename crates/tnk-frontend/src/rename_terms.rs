//! Grammar-aware operator renaming for statement term-bubbles (the `op _,_ to _;_` case).
//!
//! A renaming `op _,_ to _;_` must rewrite only the *operator* occurrences of `,` in a term, never the
//! argument separators of an enclosing prefix application — a distinction only the grammar can make:
//! `delete(E, (E, S))` has an arg-separator comma and an operator comma at the *same* paren depth, and
//! `if E in S' then E, A else A fi` hides an operator comma inside a mixfix operand. So we build the
//! source module's grammar, parse each bubble, and surgically replace the literal fragment tokens at the
//! parse-identified positions of the renamed operators — leaving every other token (and the bubble's
//! exact shape) untouched. Single-token op renames (`empty to none`) ride the same path, identified by
//! parse rather than blind text match.

use crate::cfparser::compile::CompiledGrammar;
use crate::cfparser::forest::PTree;
use crate::cfparser::{ParseEffort, earley, forest};
use crate::grammar::build::build_grammar;
use crate::grammar::{Action, GSym, Nt};
use crate::lex::{Frag, Interner, TokKind, Token, split_mixfix};
use crate::load::{
    ConditionPiece, condition_pieces, fill_empty_object_attributes, install_identities,
};
use crate::sig::build_sig::{build_module, canonical_name, resolve_sort};
use crate::sig::syntax::BuiltModule;
use crate::surface::ast::PreModule;
use crate::surface::sort_spelling::{kind_components, kind_representative};
use std::collections::{HashMap, HashSet};

type RenameTarget = (Option<usize>, Vec<String>);
type RenameTargets = HashMap<String, Vec<RenameTarget>>;

/// A renamer for one import's op renamings: the source module's signature + grammar (built once from the
/// *pre-rename* declarations) plus the from-name → target-fragment map.
pub struct OpRenamer {
    built: BuiltModule,
    grammar: CompiledGrammar,
    /// from-op canonical name (`_,_`, `empty`, `f`) → the candidate renames of that name: each an optional
    /// disambiguating **arity** (`Some(2)` for `op f : A B -> C to g`; `None` renames every overload) with
    /// the target op's literal fragment texts, in order (`_;_` → `[";"]`, `none` → `["none"]`).
    targets: RenameTargets,
}

/// Build the signature and grammar that source bubbles are parsed against. Identity terms are installed
/// as in a loaded module, so a bubble that omits an object's attribute set (`< O : C | >`) is completed
/// with the attribute-set identity before parsing, exactly as the statement loader completes it
/// ([`fill_empty_object_attributes`]).
fn build_syntax_module(
    pm: &PreModule,
    interner: &mut Interner,
) -> Result<(BuiltModule, CompiledGrammar), String> {
    let mut syntax = pm.clone();
    for operator in &mut syntax.ops {
        let is_host = operator
            .attrs
            .special
            .as_ref()
            .and_then(|special| special.id_hook.as_ref())
            .is_some_and(|(class, _)| class == "HostFunctionSymbol");
        if is_host {
            // Renaming needs only the pre-transform grammar. Capability validation and attachment happen
            // once, when the transformed module is built for execution.
            operator.attrs.special = None;
        }
    }
    let mut built = build_module(&syntax, interner)?;
    let grammar = CompiledGrammar::compile(&build_grammar(&built, interner));
    // Identities serve only that completion here. A bad identity term is diagnosed by the build of the
    // module that is executed; here it leaves the remaining slots reserved, which name no identity
    // constant, so a bubble that needs one is not completed.
    let _ = install_identities(&mut built, &grammar, interner);
    Ok((built, grammar))
}

impl OpRenamer {
    /// Build the grammar of `pm` (a flattened, pre-rename module) for the op renames `renames`
    /// (`(from_name, arity, to_name)` — `arity` = `Some(n)` for an arity-disambiguated rename of one
    /// overload, `None` for a plain rename of every overload). Returns `None` if there is nothing to do; an
    /// `Err` only if building the source module/grammar fails.
    pub fn new(
        pm: &PreModule,
        renames: &[(String, Option<usize>, String)],
        interner: &mut Interner,
    ) -> Result<Option<Self>, String> {
        if renames.is_empty() {
            return Ok(None);
        }
        let mut targets = RenameTargets::new();
        for (from, arity, to) in renames {
            targets
                .entry(from.clone())
                .or_default()
                .push((*arity, literal_frags(to, interner)));
        }
        let (built, grammar) = build_syntax_module(pm, interner)?;
        Ok(Some(Self {
            built,
            grammar,
            targets,
        }))
    }

    /// Rewrite one term bubble into a fresh token vector, replacing each renamed operator's literal
    /// fragments. A bubble that does not parse as a term is returned unchanged because operator identity
    /// is undefined there. An omitted object attribute set is completed before parsing, as the statement
    /// loader completes it, and an edited bubble keeps that explicit identity.
    pub fn rewrite(&self, bubble: &[Token], interner: &mut Interner) -> Vec<Token> {
        if bubble.is_empty() {
            return bubble.to_vec();
        }
        let tokens = fill_empty_object_attributes(bubble, &self.built, interner);
        let tree = match parse_term(&tokens, &self.grammar, interner) {
            Ok(t) => t,
            Err(_) => return bubble.to_vec(),
        };
        let mut edits: Vec<(usize, String)> = Vec::new();
        self.collect(&tree, &tokens, interner, &mut edits);
        if edits.is_empty() {
            return bubble.to_vec();
        }
        let new_syms: Vec<(usize, _)> = edits
            .iter()
            .map(|(pos, text)| (*pos, interner.intern(text)))
            .collect();
        // The edit positions index the completed tokens.
        let mut out = tokens.into_owned();
        for (pos, sym) in new_syms {
            out[pos].sym = sym;
        }
        out
    }

    /// Walk `t`, recording `(token-position, replacement-text)` for each literal fragment of a renamed
    /// operator. At a `MakeTerm(sym)` node whose symbol is renamed, the literal fragments are the
    /// terminal positions of the production's rhs, found by tiling `[start, end)` with child spans. A
    /// terminal consumes one token and a nonterminal jumps to the next child's end. A compact
    /// `MakeIter(sym)` token is rewritten as a unit (`g^N` → `h^N`), preserving its scalar count.
    fn collect(
        &self,
        t: &PTree,
        bubble: &[Token],
        interner: &Interner,
        edits: &mut Vec<(usize, String)>,
    ) {
        let prod = &self.grammar.prods[t.prod as usize];
        if let Action::MakeIter(sym) = prod.action {
            let name = self.built.engine.symbol(sym).name();
            let target = self.targets.get(name).and_then(|cands| {
                cands
                    .iter()
                    .find(|(a, _)| *a == Some(1))
                    .or_else(|| cands.iter().find(|(a, _)| a.is_none()))
                    .and_then(|(_, frags)| frags.as_slice().first())
            });
            if let Some(target) = target
                && let Some((_, count)) = bubble[t.start].text(interner).rsplit_once('^')
            {
                edits.push((t.start, format!("{target}^{count}")));
            }
        }
        if let Action::MakeTerm(sym) = prod.action {
            let name = self.built.engine.symbol(sym).name();
            // This node's arity = the number of argument nonterminals in the production. An
            // arity-disambiguated candidate matches only that arity; a plain (`None`) candidate matches any.
            let arity = prod.rhs.iter().filter(|g| matches!(g, GSym::N(_))).count();
            if let Some(target) = self.targets.get(name).and_then(|cands| {
                cands
                    .iter()
                    .find(|(a, _)| *a == Some(arity))
                    .or_else(|| cands.iter().find(|(a, _)| a.is_none()))
                    .map(|(_, frags)| frags)
            }) {
                let mut cursor = t.start;
                let mut child = 0;
                let mut frag = 0;
                for g in &prod.rhs {
                    match g {
                        GSym::T(_) => {
                            if let Some(text) = target.get(frag) {
                                edits.push((cursor, (*text).to_string()));
                            }
                            frag += 1;
                            cursor += 1;
                        }
                        GSym::N(_) => {
                            cursor = t.nt_children[child].end;
                            child += 1;
                        }
                    }
                }
            }
        }
        for c in &t.nt_children {
            self.collect(c, bubble, interner, edits);
        }
    }
}

/// A grammar-aware operator-map substituter for **view** op→op instantiation, where the source and target
/// operators may have *different* fixity (`op f to _+_`, `op _#_ to g`, `op _#_ to _+_`) — a distinction a
/// token substitution cannot express. Like [`OpRenamer`] it builds the source (parameterized) module's
/// grammar and parses each statement bubble, but instead of surgically swapping an operator's literal
/// fragments it **reconstructs** each mapped operator application in the *target* operator's syntax: a
/// prefix target `g` emits `g ( a , b )`, a mixfix target `_+_` emits `( ( a ) + ( b ) )`, wrapped around
/// the (recursively rewritten) argument sub-bubbles. Every non-mapped subterm is reproduced token-for-token,
/// so the bubble's shape is preserved wherever no mapped operator occurs.
///
/// Plain single-token maps stay on the caller's textual path. Fixity-changing maps and
/// signature-disambiguated maps come here: the latter resolve their source declaration profile to the
/// same symbol identity carried by each parse-tree action.
///
/// The target of a reconstructed view operator map is another operator (with a possibly different fixity)
/// or a **term template** for an op→term map with variable arguments.
#[derive(Clone)]
pub enum ReconTarget {
    /// op→op: the target operator's canonical name (`g`, `_+_`) — the application is re-emitted in its syntax.
    Op(String),
    /// op(A, B, …)→term: a term template. `formals` are the from-pattern's argument variable base-names in
    /// order (`lt(A, B)` ⇒ `["A", "B"]`); `template` is the target term's tokens (`A < B`). At each
    /// occurrence, every template variable whose base-name is a formal is replaced by the (rewritten,
    /// parenthesized) actual argument at that position.
    Term {
        formals: Vec<String>,
        template: Vec<Token>,
    },
}

/// One grammar-aware view operator map. `dom_range` selects one source overload by its resolved signature;
/// `None` maps every source symbol with the canonical `source` name.
#[derive(Clone)]
pub struct ViewOpMap {
    pub source: String,
    pub dom_range: Option<(Vec<String>, String)>,
    pub target: ReconTarget,
}

/// The sort spellings a signature-qualified [`ViewOpMap`] profile may use.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ProfileSorts {
    /// Declared sort names only; a kind spelling is an unknown source sort. Operator renamings use this:
    /// their declaration-side selection compares spelled profiles, so a kind profile resolved here could
    /// rename statement occurrences without the declaration they belong to.
    SortsOnly,
    /// Sort names and kind spellings (`[Elt]`, `[A,B]`); a kind spelling denotes the error sort of the
    /// kind of its first component. View operator maps use this.
    SortsAndKinds,
}

/// Rewrite the referenced operator at the head of an `op-hook` signature. Signature-qualified maps
/// compare complete structured sort/kind names; both source arrows accepted by the surface syntax are
/// recognized. Operator-to-term maps cannot name an operator hook and are deliberately left unchanged
/// for binding validation to reject.
pub fn rewrite_op_hook_signature(
    signature: &[Token],
    maps: &[ViewOpMap],
    interner: &mut Interner,
) -> Vec<Token> {
    rewrite_op_hook_signature_by(
        signature,
        maps,
        |(expected_domain, expected_range), domain, range| {
            expected_domain == domain && expected_range == range
        },
        interner,
    )
}

/// [`rewrite_op_hook_signature`], with `selects(profile, domain, range)` deciding whether a
/// signature-qualified map's profile selects the referenced declaration `name : domain -> range`. A
/// selecting signature-qualified map takes precedence over a plain map of the same name, as in
/// [`ViewOpSubst`]'s statement rewrite.
pub fn rewrite_op_hook_signature_by(
    signature: &[Token],
    maps: &[ViewOpMap],
    selects: impl Fn(&(Vec<String>, String), &[String], &str) -> bool,
    interner: &mut Interner,
) -> Vec<Token> {
    let Some((name, domain, range, colon)) = hook_signature_parts(signature, interner) else {
        return signature.to_vec();
    };
    let qualified = maps.iter().find(|map| {
        map.source == name
            && map
                .dom_range
                .as_ref()
                .is_some_and(|profile| selects(profile, &domain, &range))
    });
    let Some(map) = qualified.or_else(|| {
        maps.iter()
            .find(|map| map.source == name && map.dom_range.is_none())
    }) else {
        return signature.to_vec();
    };
    let ReconTarget::Op(target) = &map.target else {
        return signature.to_vec();
    };
    let mut rewritten = crate::lex::tokenize(target, interner);
    rewritten.extend_from_slice(&signature[colon..]);
    rewritten
}

fn hook_signature_parts(
    signature: &[Token],
    interner: &Interner,
) -> Option<(String, Vec<String>, String, usize)> {
    let text = |token: &Token| interner.resolve(token.sym);
    let colon = signature.iter().position(|token| text(token) == ":")?;
    let arrow = signature
        .iter()
        .enumerate()
        .skip(colon + 1)
        .find_map(|(index, token)| matches!(text(token), "->" | "~>").then_some(index))?;
    let join = |tokens: &[Token]| tokens.iter().map(&text).collect::<String>();
    let consume_type = |start: usize, limit: usize| -> Option<usize> {
        if start >= limit {
            return None;
        }
        let mut index = start;
        if text(&signature[index]) == "[" {
            let mut depth = 0i32;
            while index < limit {
                match text(&signature[index]) {
                    "[" => depth += 1,
                    "]" => depth -= 1,
                    _ => {}
                }
                index += 1;
                if depth == 0 {
                    break;
                }
            }
            (depth == 0).then_some(index)
        } else {
            index += 1;
            while index < limit && text(&signature[index]) == "{" {
                let mut depth = 0i32;
                while index < limit {
                    match text(&signature[index]) {
                        "{" => depth += 1,
                        "}" => depth -= 1,
                        _ => {}
                    }
                    index += 1;
                    if depth == 0 {
                        break;
                    }
                }
                if depth != 0 {
                    return None;
                }
            }
            Some(index)
        }
    };

    let name = canonical_name(&signature[..colon], interner);
    let range_start = arrow + 1;
    let range_end = consume_type(range_start, signature.len())?;
    let range = join(&signature[range_start..range_end]);
    let mut domain = Vec::new();
    let mut index = colon + 1;
    while index < arrow {
        let start = index;
        index = consume_type(start, arrow)?;
        domain.push(join(&signature[start..index]));
    }
    Some((name, domain, range, colon))
}

#[derive(Clone)]
struct LexicalFallback {
    source: Vec<Frag>,
    target: ReconTarget,
}

pub struct ViewOpSubst {
    built: BuiltModule,
    grammar: CompiledGrammar,
    /// Signature-disambiguated maps resolved to the parser's source symbol identity.
    symbol_targets: HashMap<tnk_core::symbol::SymbolId, ReconTarget>,
    /// Plain maps apply to every overload of their canonical source name.
    name_targets: HashMap<String, ReconTarget>,
    /// A token-local fallback for mixfix occurrences inside compound bubbles the standalone term parser
    /// cannot accept (notably juxtaposed object configurations and `if` branches). Only sources with a
    /// literal fragment are registered: an all-hole source such as `__` would match every adjacent token
    /// pair.
    fallbacks: Vec<LexicalFallback>,
}

impl ViewOpSubst {
    /// Build over `pm` (the source parameterized module, flattened with its parameter copies so the theory
    /// operators and its variables are in scope). `Ok(None)` if `maps` is empty; an exact source profile is
    /// resolved to the same symbol identity carried by the source grammar. `profile_sorts` says whether a
    /// profile may spell a sort as a kind.
    pub fn new(
        pm: &PreModule,
        maps: &[ViewOpMap],
        profile_sorts: ProfileSorts,
        interner: &mut Interner,
    ) -> Result<Option<Self>, String> {
        if maps.is_empty() {
            return Ok(None);
        }
        let (built, grammar) = build_syntax_module(pm, interner)?;
        let resolve = |sort: &String| {
            let resolved = match profile_sorts {
                ProfileSorts::SortsAndKinds if kind_components(sort).is_some() => {
                    let sorts = built.engine.sorts();
                    built
                        .sorts
                        .get(kind_representative(sort))
                        .map(|&member| sorts.error_sort(sorts.kind_of(member)))
                }
                _ => built.sorts.get(sort).copied(),
            };
            resolved.ok_or_else(|| format!("unknown source sort `{sort}` in view operator map"))
        };
        let mut symbol_targets = HashMap::new();
        let mut name_targets = HashMap::new();
        for map in maps {
            let Some((domain, range)) = &map.dom_range else {
                name_targets.insert(map.source.clone(), map.target.clone());
                continue;
            };
            let domain_ids: Vec<_> = domain.iter().map(resolve).collect::<Result<_, _>>()?;
            let range_id = resolve(range)?;
            let symbols: HashSet<_> = built
                .op_profiles
                .iter()
                .filter(|profile| {
                    built.engine.symbol(profile.symbol).name() == map.source
                        && profile.domain == domain_ids
                        && profile.range == range_id
                })
                .map(|profile| profile.symbol)
                .collect();
            if symbols.is_empty() {
                return Err(format!(
                    "source operator `{}` : {} -> {} is not defined",
                    map.source,
                    domain.join(" "),
                    range
                ));
            }
            for symbol in symbols {
                if symbol_targets.insert(symbol, map.target.clone()).is_some() {
                    return Err(format!(
                        "conflicting view mappings select source operator `{}`",
                        map.source
                    ));
                }
            }
        }
        let fallbacks = maps
            .iter()
            .filter(|map| map.dom_range.is_none())
            .filter_map(|map| {
                let fragments = split_mixfix(&map.source, interner);
                let has_hole = fragments
                    .iter()
                    .any(|fragment| matches!(fragment, Frag::Hole));
                let has_literal = fragments
                    .iter()
                    .any(|fragment| matches!(fragment, Frag::Tok(_)));
                let changes = !matches!(&map.target, ReconTarget::Op(name) if name == &map.source);
                (has_hole && has_literal && changes).then(|| LexicalFallback {
                    source: fragments,
                    target: map.target.clone(),
                })
            })
            .collect();
        Ok(Some(Self {
            built,
            grammar,
            symbol_targets,
            name_targets,
            fallbacks,
        }))
    }

    fn target(&self, symbol: tnk_core::symbol::SymbolId, name: &str) -> Option<&ReconTarget> {
        self.symbol_targets
            .get(&symbol)
            .or_else(|| self.name_targets.get(name))
    }

    /// Whether a signature-qualified map's `profile` selects the same-named source declaration
    /// `domain -> range`: whether that declaration belongs to the overload family (§1.2) the profile names,
    /// with the same arity and each domain sort and the range in the profile's kinds. This is the family
    /// whose applications the statement rewrite reconstructs through its source symbol.
    pub fn selects_family(
        &self,
        (profile_domain, profile_range): &(Vec<String>, String),
        domain: &[String],
        range: &str,
    ) -> bool {
        profile_domain.len() == domain.len()
            && profile_domain
                .iter()
                .zip(domain)
                .all(|(selector, sort)| self.same_kind(selector, sort))
            && self.same_kind(profile_range, range)
    }

    /// Whether two sort names, or kind names such as `[S]`, lie in one kind of the source module. A name the
    /// source module does not declare matches only its own spelling.
    fn same_kind(&self, left: &str, right: &str) -> bool {
        let kind = |name: &str| {
            resolve_sort(&self.built.engine, &self.built.sorts, name)
                .ok()
                .map(|sort| self.built.engine.sorts().kind_of(sort))
        };
        left == right || matches!((kind(left), kind(right)), (Some(l), Some(r)) if l == r)
    }

    /// Rewrite one term bubble. Grammar reconstruction handles arbitrary argument terms. If the bubble is
    /// not a standalone term (for example a juxtaposed object configuration), a conservative lexical path
    /// still rewrites non-disambiguated, literal-anchored mixfix occurrences whose arguments are single
    /// tokens. See [`Self::rewrite_checked`].
    pub fn rewrite(&self, bubble: &[Token], interner: &mut Interner) -> Vec<Token> {
        self.rewrite_checked(bubble, interner).0
    }

    /// [`Self::rewrite`], also reporting whether every mapped occurrence was reconstructed from the source
    /// parse. Callers with token-level fallbacks of their own must not apply them to such a result: a
    /// remaining source spelling there is not an occurrence (a variable, an argument separator, or another
    /// map's reconstructed target).
    ///
    /// The lexical path runs only on a bubble that does not parse as a term. A parsed bubble needs no
    /// lexical pass, because reconstruction has already rewritten every mapped occurrence, and a lexical
    /// pass cannot tell an operator fragment from an argument separator spelled the same way: under
    /// `op _,_ to _;_` it would turn the comma of `insert(E, S)` into an application. An ambiguous bubble
    /// is reconstructed only when its two extracted readings give the same tokens; otherwise it is
    /// returned unchanged.
    ///
    /// The parse sees the tokens the statement loader parses: an omitted object attribute set
    /// (`< O : C | >`) is first completed with the attribute-set identity. A reconstruction keeps that
    /// explicit identity (`< O : C | none >`), which denotes the same term; a bubble in which no mapped
    /// operator occurs keeps its own tokens.
    pub fn rewrite_checked(&self, bubble: &[Token], interner: &mut Interner) -> (Vec<Token>, bool) {
        if bubble.is_empty() {
            return (Vec::new(), false);
        }
        let tokens = fill_empty_object_attributes(bubble, &self.built, interner);
        let parsed = match parse_forest(&tokens, &self.grammar, interner) {
            Ok(parsed) => parsed,
            Err(_) => return (self.rewrite_lexical(bubble, interner), false),
        };
        let same_tokens = |left: &[Token], right: &[Token]| {
            left.iter().map(|t| t.sym).eq(right.iter().map(|t| t.sym))
        };
        let rewritten = self.emit(&parsed.tree, &tokens, interner);
        let reading_independent = !parsed.ambiguous
            || parsed.alternative.is_some_and(|alternative| {
                same_tokens(&self.emit(&alternative, &tokens, interner), &rewritten)
            });
        if !reading_independent {
            (bubble.to_vec(), false)
        } else if same_tokens(&rewritten, &tokens) {
            (bubble.to_vec(), true)
        } else {
            (rewritten, true)
        }
    }

    /// Rewrite a condition bubble term by term. A whole condition is not a term, so [`Self::rewrite`] would
    /// reconstruct none of its operator applications. The bubble is split exactly as the condition parser
    /// splits it ([`condition_pieces`]); each term is rewritten as a term bubble, and the connectives and a
    /// sort test's sort are kept as written.
    pub fn rewrite_condition(&self, bubble: &[Token], interner: &mut Interner) -> Vec<Token> {
        let mut out = Vec::with_capacity(bubble.len());
        for piece in condition_pieces(bubble, interner) {
            match piece {
                ConditionPiece::Term(term) => out.extend(self.rewrite(term, interner)),
                ConditionPiece::Sort(sort) => out.extend_from_slice(sort),
                ConditionPiece::Separator(token) => out.push(token),
            }
        }
        out
    }

    fn rewrite_lexical(&self, bubble: &[Token], interner: &mut Interner) -> Vec<Token> {
        let mut out = Vec::with_capacity(bubble.len());
        let mut cursor = 0;
        while cursor < bubble.len() {
            let matched = self.fallbacks.iter().find_map(|fallback| {
                let end = cursor.checked_add(fallback.source.len())?;
                let candidate = bubble.get(cursor..end)?;
                let mut args = Vec::new();
                for (fragment, token) in fallback.source.iter().zip(candidate) {
                    match fragment {
                        Frag::Tok(expected) if expected != &token.sym => return None,
                        Frag::Tok(_) => {}
                        Frag::Hole => args.push(vec![*token]),
                    }
                }
                Some((end, fallback, args))
            });
            if let Some((end, fallback, args)) = matched {
                match &fallback.target {
                    ReconTarget::Op(name) => {
                        out.extend(emit_application(name, &args, bubble, interner))
                    }
                    ReconTarget::Term { formals, template } => {
                        out.extend(emit_template(formals, template, &args, bubble, interner))
                    }
                }
                cursor = end;
            } else {
                out.push(bubble[cursor]);
                cursor += 1;
            }
        }
        out
    }

    /// Re-serialize the parse tree `t`, substituting a mapped operator's application with the target
    /// operator's syntax and reproducing everything else token-for-token (the terminal positions are tiled
    /// exactly as in [`OpRenamer::collect`]: a terminal consumes one token, a nonterminal jumps to its
    /// child's end).
    fn emit(&self, t: &PTree, bubble: &[Token], interner: &mut Interner) -> Vec<Token> {
        let prod = &self.grammar.prods[t.prod as usize];
        if let Action::MakeIter(sym) = prod.action {
            let name = self.built.engine.symbol(sym).name();
            let count = bubble[t.start]
                .text(interner)
                .rsplit_once('^')
                .map(|(_, count)| count.to_string());
            if let (Some(ReconTarget::Op(target)), Some(count)) =
                (self.target(sym, name).cloned(), count)
            {
                let args: Vec<Vec<Token>> = t
                    .nt_children
                    .iter()
                    .map(|c| self.emit(c, bubble, interner))
                    .collect();
                let mut emitted =
                    emit_application(&format!("{target}^{count}"), &args, bubble, interner);
                // `emit_application` synthesizes ordinary operator tokens; this one remains an ITER_SYMBOL.
                // Preserve the parsed source token's semantic class while changing only its rooted symbol.
                if let Some(head) = emitted.first_mut() {
                    head.kind = bubble[t.start].kind;
                }
                return emitted;
            }
        }
        if let Action::MakeTerm(sym) = prod.action {
            let name = self.built.engine.symbol(sym).name();
            if let Some(target) = self.target(sym, name).cloned() {
                let args: Vec<Vec<Token>> = t
                    .nt_children
                    .iter()
                    .map(|c| self.emit(c, bubble, interner))
                    .collect();
                return match target {
                    ReconTarget::Op(name) => emit_application(&name, &args, bubble, interner),
                    ReconTarget::Term { formals, template } => {
                        emit_template(&formals, &template, &args, bubble, interner)
                    }
                };
            }
        }
        let mut out = Vec::new();
        let mut cursor = t.start;
        let mut child = 0;
        for g in &prod.rhs {
            match g {
                GSym::T(_) => {
                    out.push(bubble[cursor]);
                    cursor += 1;
                }
                GSym::N(_) => {
                    let c = &t.nt_children[child];
                    out.extend(self.emit(c, bubble, interner));
                    cursor = c.end;
                    child += 1;
                }
            }
        }
        out
    }
}

/// Emit an application of the operator named `target` to `args` (each an already-rewritten sub-bubble), in
/// `target`'s mixfix syntax: `g ( a , b )` for a prefix/constant name, `( ( a ) + ( b ) )` for a mixfix
/// name (redundant parentheses guard precedence when the result is re-parsed against the instance grammar).
/// `line` for synthesized tokens is borrowed from the first available argument/bubble token.
fn emit_application(
    target: &str,
    args: &[Vec<Token>],
    bubble: &[Token],
    interner: &mut Interner,
) -> Vec<Token> {
    let frags = split_mixfix(target, interner);
    let line = args
        .iter()
        .flatten()
        .next()
        .or_else(|| bubble.first())
        .map(|t| t.line)
        .unwrap_or(0);
    let lp = Token {
        sym: interner.intern("("),
        line,
        kind: TokKind::Punct,
    };
    let rp = Token {
        sym: interner.intern(")"),
        line,
        kind: TokKind::Punct,
    };
    let comma = Token {
        sym: interner.intern(","),
        line,
        kind: TokKind::Punct,
    };
    let mut out = Vec::new();
    if frags.iter().any(|f| matches!(f, Frag::Hole)) {
        out.push(lp);
        let mut ai = 0;
        for f in &frags {
            match f {
                Frag::Tok(s) => out.push(Token {
                    sym: *s,
                    line,
                    kind: TokKind::Ident,
                }),
                Frag::Hole => {
                    out.push(lp);
                    if let Some(a) = args.get(ai) {
                        out.extend_from_slice(a);
                    }
                    out.push(rp);
                    ai += 1;
                }
            }
        }
        out.push(rp);
    } else {
        for f in &frags {
            if let Frag::Tok(s) = f {
                out.push(Token {
                    sym: *s,
                    line,
                    kind: TokKind::Ident,
                });
            }
        }
        if !args.is_empty() {
            out.push(lp);
            for (k, a) in args.iter().enumerate() {
                out.extend_from_slice(a);
                out.push(if k + 1 == args.len() { rp } else { comma });
            }
        }
    }
    out
}

/// Emit a term template for an op→term view map (`op lt(A, B) to term A < B`), substituting each formal
/// variable in `template` with the (already-rewritten) actual argument at the matching position. A template
/// token is a placeholder iff its base-name (the text before any `:sort` suffix) is one of `formals`; the
/// substituted argument is wrapped in parentheses so it re-parses at any precedence. Non-placeholder tokens
/// (operators, literals, the target term's own free variables) are reproduced verbatim.
fn emit_template(
    formals: &[String],
    template: &[Token],
    args: &[Vec<Token>],
    bubble: &[Token],
    interner: &mut Interner,
) -> Vec<Token> {
    let line = args
        .iter()
        .flatten()
        .next()
        .or_else(|| bubble.first())
        .map(|t| t.line)
        .unwrap_or(0);
    let lp = Token {
        sym: interner.intern("("),
        line,
        kind: TokKind::Punct,
    };
    let rp = Token {
        sym: interner.intern(")"),
        line,
        kind: TokKind::Punct,
    };
    let mut out = Vec::new();
    for t in template {
        let text = interner.resolve(t.sym);
        let base = text.split(':').next().unwrap_or(text);
        if let Some(idx) = formals.iter().position(|f| f == base)
            && let Some(arg) = args.get(idx)
        {
            out.push(lp);
            out.extend_from_slice(arg);
            out.push(rp);
        } else {
            out.push(*t);
        }
    }
    out
}

/// The literal (non-hole) fragment texts of a mixfix op name, in order (`_;_` → `[";"]`, `none` →
/// `["none"]`). Also used by the module system to rename an op *declaration*'s name tokens.
pub fn literal_frags(name: &str, interner: &mut Interner) -> Vec<String> {
    split_mixfix(name, interner)
        .into_iter()
        .filter_map(|f| match f {
            Frag::Tok(s) => Some(interner.resolve(s).to_string()),
            Frag::Hole => None,
        })
        .collect()
}

/// Parse a term token bubble at the universal start symbol (the statement/pattern path, sans build),
/// keeping the second reading of an ambiguous bubble.
fn parse_forest(
    tokens: &[Token],
    g: &CompiledGrammar,
    i: &Interner,
) -> Result<forest::Parse, String> {
    let mut effort = ParseEffort::default();
    let chart = earley::parse(g, tokens, Nt::Term, i, &mut effort)
        .map_err(|e| format!("parse effort limit exceeded at token {}", e.at))?;
    forest::extract(g, &chart, tokens.len(), Nt::Term, &mut effort).map_err(|e| e.to_string())
}

/// Parse a term token bubble to its unique parse tree.
fn parse_term(tokens: &[Token], g: &CompiledGrammar, i: &Interner) -> Result<PTree, String> {
    let parsed = parse_forest(tokens, g, i)?;
    if parsed.ambiguous {
        return Err("ambiguous".into());
    }
    Ok(parsed.tree)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lex::tokenize;
    use crate::surface::parser::Parser;

    fn iter_module(i: &mut Interner) -> PreModule {
        let source = tokenize(
            "fmod ITER-RENAME is sort S . op a : -> S [ctor] . \
             op g : S -> S [ctor iter] . endfm",
            i,
        );
        Parser::new(&source, i)
            .parse_source()
            .expect("parse source")
            .modules
            .remove(0)
    }

    #[test]
    fn op_renamer_preserves_compact_iter_count() {
        let mut i = Interner::new();
        let pm = iter_module(&mut i);
        let mapper = OpRenamer::new(&pm, &[("g".into(), None, "h".into())], &mut i)
            .expect("build")
            .expect("mapper");
        let bubble = tokenize("g^1000000(a)", &mut i);
        let rewritten = mapper.rewrite(&bubble, &mut i);
        let text: String = rewritten.iter().map(|t| i.resolve(t.sym)).collect();
        assert_eq!(text, "h^1000000(a)");
    }

    #[test]
    fn view_substitution_preserves_compact_iter_count() {
        let mut i = Interner::new();
        let pm = iter_module(&mut i);
        let mapper = ViewOpSubst::new(
            &pm,
            &[ViewOpMap {
                source: "g".into(),
                dom_range: None,
                target: ReconTarget::Op("h".into()),
            }],
            ProfileSorts::SortsAndKinds,
            &mut i,
        )
        .expect("build")
        .expect("mapper");
        let bubble = tokenize("g^1000000(a)", &mut i);
        let rewritten = mapper.rewrite(&bubble, &mut i);
        let text: String = rewritten.iter().map(|t| i.resolve(t.sym)).collect();
        assert_eq!(text, "h^1000000(a)");
    }

    fn source_module(source: &str, i: &mut Interner) -> PreModule {
        let source = tokenize(source, i);
        Parser::new(&source, i)
            .parse_source()
            .expect("parse source")
            .modules
            .remove(0)
    }

    fn op_map(source: &str, target: &str) -> ViewOpMap {
        ViewOpMap {
            source: source.into(),
            dom_range: None,
            target: ReconTarget::Op(target.into()),
        }
    }

    /// Rewrite `bubble` and render the result with spaces between tokens, plus the reconstruction flag.
    fn substituted(mapper: &ViewOpSubst, bubble: &str, i: &mut Interner) -> (String, bool) {
        let bubble = tokenize(bubble, i);
        let (rewritten, reconstructed) = mapper.rewrite_checked(&bubble, i);
        let text = rewritten
            .iter()
            .map(|t| i.resolve(t.sym))
            .collect::<Vec<_>>()
            .join(" ");
        (text, reconstructed)
    }

    /// `op _,_ to _;_` rewrites only parsed `_,_` applications. A prefix application's argument separator
    /// is the same token, so no lexical pass may run over a parsed bubble.
    #[test]
    fn view_substitution_keeps_prefix_argument_separators() {
        let mut i = Interner::new();
        let pm = source_module(
            "fmod COMMA-SRC is sorts E S . subsort E < S . op e : -> E [ctor] . \
             op _,_ : S S -> S [ctor assoc comm] . op ins : E S -> S . \
             var X : E . var Y : S . endfm",
            &mut i,
        );
        let mapper = ViewOpSubst::new(
            &pm,
            &[op_map("_,_", "_;_")],
            ProfileSorts::SortsAndKinds,
            &mut i,
        )
        .expect("build")
        .expect("mapper");
        assert_eq!(
            substituted(&mapper, "ins(X, Y)", &mut i),
            ("ins ( X , Y )".into(), true)
        );
        assert_eq!(
            substituted(&mapper, "X, Y", &mut i),
            ("( ( X ) ; ( Y ) )".into(), true)
        );
        assert_eq!(
            substituted(&mapper, "ins(X, (X, Y))", &mut i),
            ("ins ( X , ( ( ( X ) ; ( Y ) ) ) )".into(), true)
        );
    }

    /// A bubble that is ambiguous at the universal start symbol (here `f` and `p` have one overload per
    /// kind) is still a term, so the lexical pass must not run on it. Its reconstruction is kept when both
    /// readings agree and the bubble is left unchanged when they do not.
    #[test]
    fn ambiguous_bubble_keeps_only_reading_independent_reconstruction() {
        let mut i = Interner::new();
        let pm = source_module(
            "fmod AMBIGUOUS-SRC is sorts A B C . op b : -> B . \
             op _+_ : B B -> B . op _,_ : B B -> B [assoc] . \
             op f : B -> A . op f : B -> C . op p : B B -> A . op p : B B -> C . \
             vars X Y : B . endfm",
            &mut i,
        );
        let mapper = ViewOpSubst::new(
            &pm,
            &[op_map("_+_", "_*_"), op_map("_,_", "_;_")],
            ProfileSorts::SortsOnly,
            &mut i,
        )
        .expect("build")
        .expect("mapper");
        assert_eq!(
            substituted(&mapper, "p(X, Y)", &mut i),
            ("p ( X , Y )".into(), true)
        );
        assert_eq!(
            substituted(&mapper, "f(X + Y)", &mut i),
            ("f ( ( ( X ) * ( Y ) ) )".into(), true)
        );

        let selective = ViewOpSubst::new(
            &pm,
            &[ViewOpMap {
                source: "f".into(),
                dom_range: Some((vec!["B".into()], "A".into())),
                target: ReconTarget::Op("g".into()),
            }],
            ProfileSorts::SortsOnly,
            &mut i,
        )
        .expect("build")
        .expect("mapper");
        assert_eq!(
            substituted(&selective, "f(X)", &mut i),
            ("f ( X )".into(), false),
            "the readings disagree on whether the mapped overload occurs"
        );
    }

    /// A condition is not a term, so it is rewritten term by term, split as the condition parser splits
    /// it: every side of `=`, `:=`, and `=>`, a sort test's subject, and a bare Boolean fragment are
    /// reconstructed, while the connectives and a sort test's sort are kept.
    #[test]
    fn view_substitution_rewrites_condition_terms() {
        let mut i = Interner::new();
        let pm = source_module(
            "mod COND-SRC is sorts S B . ops a b : -> S [ctor] . op tt : -> B . \
             op lt : S S -> B . op _+_ : S S -> S . var X : S . endm",
            &mut i,
        );
        let mapper = ViewOpSubst::new(
            &pm,
            &[op_map("lt", "_<<_"), op_map("_+_", "plus")],
            ProfileSorts::SortsAndKinds,
            &mut i,
        )
        .expect("build")
        .expect("mapper");
        let bubble = tokenize(
            "lt(X, a) = tt /\\ X := a + b /\\ a + X : S /\\ lt(a, b) /\\ X + a => b",
            &mut i,
        );
        let rewritten = mapper.rewrite_condition(&bubble, &mut i);
        let text = rewritten
            .iter()
            .map(|t| i.resolve(t.sym))
            .collect::<Vec<_>>()
            .join(" ");
        assert_eq!(
            text,
            "( ( X ) << ( a ) ) = tt /\\ X := plus ( a , b ) /\\ plus ( a , X ) : S /\\ \
             ( ( a ) << ( b ) ) /\\ plus ( X , a ) => b"
        );
        let unchanged = tokenize("a = b /\\ X : S", &mut i);
        assert!(
            mapper
                .rewrite_condition(&unchanged, &mut i)
                .iter()
                .map(|t| t.sym)
                .eq(unchanged.iter().map(|t| t.sym)),
            "a condition without mapped operators keeps its tokens"
        );
    }

    /// An all-hole source such as `__` has no literal anchor, so it registers no lexical fallback. Parsed
    /// juxtapositions are still reconstructed, while a bubble that is not a term is left unchanged rather
    /// than having every adjacent token pair rewritten. A literal-anchored map keeps its fallback.
    #[test]
    fn juxtaposition_map_has_no_lexical_fallback() {
        let mut i = Interner::new();
        let pm = source_module(
            "fmod JUXT-SRC is sort S . ops a b c : -> S [ctor] . \
             op __ : S S -> S [ctor assoc] . op _+_ : S S -> S . op g : S S -> S . endfm",
            &mut i,
        );
        let juxtaposition =
            ViewOpSubst::new(&pm, &[op_map("__", "_;_")], ProfileSorts::SortsOnly, &mut i)
                .expect("build")
                .expect("mapper");
        assert_eq!(
            substituted(&juxtaposition, "a b", &mut i),
            ("( ( a ) ; ( b ) )".into(), true)
        );
        assert_eq!(
            substituted(&juxtaposition, "g(a, b) = c", &mut i),
            ("g ( a , b ) = c".into(), false)
        );

        let plus = ViewOpSubst::new(
            &pm,
            &[op_map("_+_", "_*_")],
            ProfileSorts::SortsOnly,
            &mut i,
        )
        .expect("build")
        .expect("mapper");
        assert_eq!(
            substituted(&plus, "a + b = c", &mut i),
            ("( ( a ) * ( b ) ) = c".into(), false)
        );
    }

    /// A view map's kind-spelled profile selects the overload declared at that kind (through any of its
    /// sorts); operator renamings keep resolving profile sorts by sort name only.
    #[test]
    fn kind_profiles_resolve_for_view_maps_only() {
        let mut i = Interner::new();
        let source = tokenize(
            "fmod KIND-MAP is sorts A B . subsort A < B . op a : -> A . \
             op f : [A] -> [A] . op f : B B -> B . endfm",
            &mut i,
        );
        let pm = Parser::new(&source, &i)
            .parse_source()
            .expect("parse source")
            .modules
            .remove(0);
        let maps = [ViewOpMap {
            source: "f".into(),
            dom_range: Some((vec!["[B,A]".into()], "[A]".into())),
            target: ReconTarget::Op("g".into()),
        }];
        let mapper = ViewOpSubst::new(&pm, &maps, ProfileSorts::SortsAndKinds, &mut i)
            .expect("build")
            .expect("mapper");
        let bubble = tokenize("f(f(a, a))", &mut i);
        let rewritten = mapper.rewrite(&bubble, &mut i);
        let text: String = rewritten.iter().map(|t| i.resolve(t.sym)).collect();
        assert_eq!(text, "g(f(a,a))");

        let err = ViewOpSubst::new(&pm, &maps, ProfileSorts::SortsOnly, &mut i)
            .err()
            .expect("kind profile rejected");
        assert!(err.contains("unknown source sort `[B,A]`"), "got: {err}");
    }

    /// An object pattern may omit its attribute set (`< O : c | >`). The source parse completes it with
    /// the attribute-set identity, as the statement loader does, so such a bubble is a term and its mapped
    /// operators are rebuilt; the output keeps the explicit `none`, while a bubble without a mapped
    /// operator keeps its own tokens. The arity-keyed renamer edits tokens in place, so its edit after
    /// the completed position must index the completed tokens.
    #[test]
    fn empty_attribute_set_is_completed_before_the_source_parse() {
        let mut i = Interner::new();
        let pm = source_module(
            "mod OBJ-SRC is sorts Oid Cid Attribute AttributeSet Object Msg Configuration . \
             subsort Attribute < AttributeSet . subsorts Object Msg < Configuration . \
             op none : -> AttributeSet [ctor] . \
             op _,_ : AttributeSet AttributeSet -> AttributeSet [ctor assoc comm id: none] . \
             op <_:_|_> : Oid Cid AttributeSet -> Object [ctor object] . \
             op __ : Configuration Configuration -> Configuration [ctor assoc comm] . \
             op c : -> Cid [ctor] . op m : Oid -> Msg [ctor] . var O : Oid . endm",
            &mut i,
        );
        let view = ViewOpSubst::new(
            &pm,
            &[op_map("m", "_!")],
            ProfileSorts::SortsAndKinds,
            &mut i,
        )
        .expect("build")
        .expect("mapper");
        assert_eq!(
            substituted(&view, "m(O) < O : c | >", &mut i),
            ("( ( O ) ! ) < O : c | none >".into(), true)
        );
        assert_eq!(
            substituted(&view, "< O : c | >", &mut i),
            ("< O : c | >".into(), true)
        );

        let renamer = OpRenamer::new(&pm, &[("m".into(), Some(1), "n".into())], &mut i)
            .expect("build")
            .expect("renamer");
        let bubble = tokenize("< O : c | > m(O)", &mut i);
        let text = renamer
            .rewrite(&bubble, &mut i)
            .iter()
            .map(|t| i.resolve(t.sym))
            .collect::<Vec<_>>()
            .join(" ");
        assert_eq!(text, "< O : c | none > n ( O )");
    }
}
