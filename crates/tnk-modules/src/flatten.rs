//! Flatten an import closure into one combined [`PreModule`] — a pure `PreModule → PreModule` transform.
//!
//! Resolve transitive imports depth-first, visiting imports before their importer and merging declarations
//! into one accumulator. Each module is included once, so import diamonds do not duplicate their shared
//! base. Sort and variable names are deduplicated; operators, subsorts, and statements retain declaration
//! order. The result has no imports and can be compiled directly.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use tnk_frontend::lex::{Interner, Token, tokenize};
use tnk_frontend::rename_terms::{
    ProfileSorts, ReconTarget, ViewOpMap, ViewOpSubst, rewrite_op_hook_signature,
};
use tnk_frontend::surface::ast::{
    Attrs, ModuleExpr, ModuleKind, OpDecl, OpMap, PreModule, RenameItem, Statement, StratExpr,
    VarDecl, ViewDecl,
};
use tnk_frontend::surface::sort_spelling::{kind_components, map_sort_spelling};

use crate::db::ModuleDb;
use crate::rename::apply_renaming;
use crate::view::ViewDb;

/// The renamable declaration bundle of a (sub-)module expression — everything a renaming `* (…)` rewrites.
#[derive(Debug)]
pub struct FlatDecls {
    pub sorts: Vec<String>,
    pub subsorts: Vec<Vec<Vec<String>>>,
    pub ops: Vec<OpDecl>,
    pub vars: Vec<VarDecl>,
    pub statements: Vec<Statement>,
    /// Whether each statement was declared by an object module or theory, parallel to
    /// [`statements`](Self::statements). Renaming and instantiation rewrite statements in place, so the
    /// flags stay aligned; the flattened module exposes them as [`PreModule::object_statements`].
    pub object_statements: Vec<bool>,
    pub strat_decls: Vec<tnk_frontend::surface::ast::StratDecl>,
    pub strat_defs: Vec<tnk_frontend::surface::ast::StratDef>,
}

/// The bare variables a statement's source scope declares: each variable name visible in its home
/// module's own grammar (imported aliases included), mapped to its sort as spelled in the donated bubble.
type VarScope = HashMap<String, String>;

/// Source variable scopes of home-less donations, parallel to an accumulator's statements and strategy
/// definitions. `Some` marks a statement or definition from a renamed or parameter-copy bundle whose bare
/// variables still mean their home declarations. `None` marks one that keeps its home tag or whose
/// variables are already inlined (an instance's own declarations).
#[derive(Default)]
struct DonationScopes {
    statements: Vec<Option<Rc<VarScope>>>,
    strat_defs: Vec<Option<Rc<VarScope>>>,
}

impl DonationScopes {
    /// Respell each scope's sorts through a renaming's sort maps, matching how the renaming rewrites the
    /// bundle's variable declarations and colon variables (`A : Tv ↦ A : Truth`).
    fn renamed(self, items: &[RenameItem]) -> Self {
        let sort_map: HashMap<&str, &str> = items
            .iter()
            .filter_map(|item| match item {
                RenameItem::Sort { from, to } => Some((from.as_str(), to.as_str())),
                _ => None,
            })
            .collect();
        if sort_map.is_empty() {
            return self;
        }
        let mut memo: HashMap<*const VarScope, Rc<VarScope>> = HashMap::new();
        let mut rename = |scope: Option<Rc<VarScope>>| {
            scope.map(|scope| {
                memo.entry(Rc::as_ptr(&scope))
                    .or_insert_with(|| {
                        Rc::new(
                            scope
                                .iter()
                                .map(|(name, sort)| {
                                    let sort = sort_map.get(sort.as_str()).copied().unwrap_or(sort);
                                    (name.clone(), sort.to_string())
                                })
                                .collect(),
                        )
                    })
                    .clone()
            })
        };
        Self {
            statements: self.statements.into_iter().map(&mut rename).collect(),
            strat_defs: self.strat_defs.into_iter().map(&mut rename).collect(),
        }
    }

    /// Inline every scoped variable named in `names` into its statement or strategy definition in `d`
    /// (parallel to these scopes) at its scope sort, and drop it from the scope, so that
    /// [`inline_rebound_vars`] leaves later bare occurrences of the name alone.
    fn inline_and_forget(
        self,
        d: &mut FlatDecls,
        names: &HashSet<String>,
        i: &mut Interner,
    ) -> Self {
        if names.is_empty() {
            return self;
        }
        // Each distinct scope splits once into the variables inlined now and the scope kept.
        let mut splits: HashMap<*const VarScope, (Rc<VarScope>, Rc<VarScope>)> = HashMap::new();
        let mut split = |scope: &Rc<VarScope>| {
            splits
                .entry(Rc::as_ptr(scope))
                .or_insert_with(|| {
                    let (now, kept): (VarScope, VarScope) = scope
                        .iter()
                        .map(|(name, sort)| (name.clone(), sort.clone()))
                        .partition(|(name, _)| names.contains(name));
                    (Rc::new(now), Rc::new(kept))
                })
                .clone()
        };
        let mut statements = Vec::with_capacity(self.statements.len());
        for (st, scope) in d.statements.iter_mut().zip(&self.statements) {
            statements.push(scope.as_ref().map(|scope| {
                let (now, kept) = split(scope);
                if now.is_empty() {
                    return scope.clone();
                }
                inline_statement_vars(st, &now, i);
                kept
            }));
        }
        let mut strat_defs = Vec::with_capacity(self.strat_defs.len());
        for (def, scope) in d.strat_defs.iter_mut().zip(&self.strat_defs) {
            strat_defs.push(scope.as_ref().map(|scope| {
                let (now, kept) = split(scope);
                if now.is_empty() {
                    return scope.clone();
                }
                inline_strat_def_vars(def, &now, i);
                kept
            }));
        }
        Self {
            statements,
            strat_defs,
        }
    }
}

/// The constants a renaming introduces: the target name of each operator rename that applies to a nullary
/// declaration in `ops` (`op n to m` for `op n : -> Tv` introduces `m`).
fn introduced_constants(
    items: &[RenameItem],
    ops: &[OpDecl],
    interner: &Interner,
) -> HashSet<String> {
    items
        .iter()
        .filter_map(|item| {
            let RenameItem::Op {
                from,
                to,
                dom_range,
                ..
            } = item
            else {
                return None;
            };
            let renames_constant = ops.iter().any(|op| {
                op.domain.is_empty()
                    && dom_range
                        .as_ref()
                        .is_none_or(|(domain, range)| domain.is_empty() && *range == op.range)
                    && op
                        .name
                        .iter()
                        .map(|token| interner.resolve(token.sym))
                        .collect::<String>()
                        == *from
            });
            renames_constant.then(|| to.clone())
        })
        .collect()
}

/// Rename a home-less bundle together with its source variable scopes. A scoped variable spelled like a
/// constant the renaming introduces (`var m : Tv` under `op n to m`) is inlined first, while a bare `m`
/// still means the variable, and leaves its scope: once renamed, a bare `m` also names the constant, and
/// no importer's variable table keeps an imported alias that a visible constant redeclares.
fn rename_bundle(
    mut decls: FlatDecls,
    scopes: DonationScopes,
    items: &[RenameItem],
    interner: &mut Interner,
) -> Result<(FlatDecls, DonationScopes), String> {
    let constants = introduced_constants(items, &decls.ops, interner);
    let scopes = scopes.inline_and_forget(&mut decls, &constants, interner);
    let renamed = apply_renaming(decls, items, interner)?;
    Ok((renamed, scopes.renamed(items)))
}

/// Accumulates merged declarations, de-duplicating sorts and variable names.
#[derive(Default)]
struct Acc {
    sorts: Vec<String>,
    sort_set: HashSet<String>,
    subsorts: Vec<Vec<Vec<String>>>,
    ops: Vec<OpDecl>,
    vars: Vec<VarDecl>,
    var_set: HashSet<String>,
    statements: Vec<Statement>,
    /// Per-statement object-module provenance ([`FlatDecls::object_statements`]), in lockstep with
    /// `statements`.
    object_statements: Vec<bool>,
    strat_decls: Vec<tnk_frontend::surface::ast::StratDecl>,
    strat_defs: Vec<tnk_frontend::surface::ast::StratDef>,
    /// Per-statement **home** module name, parallel to [`statements`](Self::statements). `Some(name)` marks
    /// a plain named-module donation whose statement may need reparsing in that module's own grammar when
    /// the flattened grammar is ambiguous. `None` marks a renamed, instantiated, or parameter-copy
    /// donation, which parses against the flattened grammar. Root statements carry `Some(root_name)`,
    /// which the loader treats as "self". Kept in lockstep with `statements`.
    statement_homes: Vec<Option<String>>,
    /// Source variable scopes of renamed and parameter-copy donations, in lockstep with `statements` and
    /// `strat_defs`. [`inline_rebound_vars`] uses them once the flattened variable table is final.
    scopes: DonationScopes,
    /// Whether renamed and parameter-copy bundles record their source variable scopes. Set for a
    /// flattening that keeps its statements ([`flatten_with_homes`], [`flatten_pre`]) and inherited by its
    /// bundle accumulators ([`Self::bundle`]). Off for a collection that only reads declarations, such as
    /// a home's variable table ([`home_var_scope`]), so computing one scope never computes another.
    track_scopes: bool,
}

impl Acc {
    /// The accumulator of a flattening whose home-less donations carry their source variable scopes.
    fn tracking_scopes() -> Self {
        Self {
            track_scopes: true,
            ..Self::default()
        }
    }

    /// A fresh accumulator for a renamed or parameter-copy bundle collected inside this one.
    fn bundle(&self) -> Self {
        Self {
            track_scopes: self.track_scopes,
            ..Self::default()
        }
    }

    /// Merge a declaration bundle, retaining each new sort and variable name once and appending every
    /// other declaration. `home` tags all statements in `d` in lockstep with the statement list.
    fn add(&mut self, d: FlatDecls, home: Option<&str>) {
        let scopes = DonationScopes {
            statements: vec![None; d.statements.len()],
            strat_defs: vec![None; d.strat_defs.len()],
        };
        self.add_scoped(d, home, scopes);
    }

    /// [`Self::add`] for a home-less renamed or parameter-copy bundle whose statements and strategy
    /// definitions carry their source variable `scopes`.
    fn add_scoped(&mut self, d: FlatDecls, home: Option<&str>, scopes: DonationScopes) {
        debug_assert_eq!(scopes.statements.len(), d.statements.len());
        debug_assert_eq!(scopes.strat_defs.len(), d.strat_defs.len());
        self.scopes.statements.extend(scopes.statements);
        self.scopes.strat_defs.extend(scopes.strat_defs);
        for s in d.sorts {
            if self.sort_set.insert(s.clone()) {
                self.sorts.push(s);
            }
        }
        self.subsorts.extend(d.subsorts);
        self.ops.extend(d.ops);
        for v in d.vars {
            let names: Vec<String> = v
                .names
                .into_iter()
                .filter(|n| self.var_set.insert(n.clone()))
                .collect();
            if !names.is_empty() {
                self.vars.push(VarDecl {
                    names,
                    sort: v.sort,
                });
            }
        }
        self.statement_homes.extend(std::iter::repeat_n(
            home.map(str::to_string),
            d.statements.len(),
        ));
        debug_assert_eq!(
            d.object_statements.len(),
            d.statements.len(),
            "object_statements parallel to statements"
        );
        self.statements.extend(d.statements);
        self.object_statements.extend(d.object_statements);
        self.strat_decls.extend(d.strat_decls);
        self.strat_defs.extend(d.strat_defs);
    }

    /// The source variable scope of each statement and strategy definition, taken before this bundle is
    /// renamed and donated without home tags. One still tagged with its home module takes that module's
    /// grammar variable table, computed once per home; a nested home-less donation keeps the scope it
    /// already carries. `root` names the module this bundle was collected from, when it is a named module:
    /// a fresh accumulator holding exactly its import closure, so its table comes from this accumulator's
    /// own declarations ([`root_var_table`]) rather than from flattening it again. Any other home is
    /// collected afresh without scopes ([`home_var_scope`]). Without scope tracking every scope is `None`.
    fn donation_scopes(
        &self,
        root: Option<&str>,
        db: &ModuleDb,
        views: &ViewDb,
        i: &mut Interner,
    ) -> DonationScopes {
        if !self.track_scopes {
            return DonationScopes {
                statements: vec![None; self.statements.len()],
                strat_defs: vec![None; self.strat_defs.len()],
            };
        }
        let mut by_home: HashMap<String, Rc<VarScope>> = HashMap::new();
        let mut scope_of = |home: &str, i: &mut Interner| -> Rc<VarScope> {
            if let Some(scope) = by_home.get(home) {
                return scope.clone();
            }
            let scope = match db.get(home) {
                Some(module) if root == Some(home) => {
                    var_scope(root_var_table(self.vars.clone(), &self.ops, module, i))
                }
                _ => home_var_scope(home, db, views, i),
            };
            let scope = Rc::new(scope);
            by_home.insert(home.to_string(), scope.clone());
            scope
        };
        let mut scopes = DonationScopes::default();
        for (home, scope) in self.statement_homes.iter().zip(&self.scopes.statements) {
            scopes.statements.push(match home {
                Some(home) => Some(scope_of(home, i)),
                None => scope.clone(),
            });
        }
        for (def, scope) in self.strat_defs.iter().zip(&self.scopes.strat_defs) {
            scopes.strat_defs.push(match &def.home {
                Some(home) => Some(scope_of(home, i)),
                None => scope.clone(),
            });
        }
        scopes
    }

    fn into_decls(self) -> FlatDecls {
        FlatDecls {
            sorts: self.sorts,
            subsorts: self.subsorts,
            ops: self.ops,
            vars: self.vars,
            statements: self.statements,
            object_statements: self.object_statements,
            strat_decls: self.strat_decls,
            strat_defs: self.strat_defs,
        }
    }
}

/// The declaration bundle a module contributes *itself* (excludes its imports — those are collected
/// separately, before it). Its statements carry the module's own object-orientation.
fn own_decls(pm: &PreModule) -> FlatDecls {
    FlatDecls {
        sorts: pm.sorts.clone(),
        subsorts: pm.subsorts.clone(),
        ops: pm.ops.clone(),
        vars: pm.vars.clone(),
        statements: pm.statements.clone(),
        object_statements: vec![pm.is_object; pm.statements.len()],
        strat_decls: pm
            .strat_decls
            .iter()
            .cloned()
            .enumerate()
            .map(|(source_index, mut decl)| {
                decl.origin = Some(pm.name.clone());
                decl.source_index = Some(source_index);
                decl.home = Some(pm.name.clone());
                decl
            })
            .collect(),
        strat_defs: pm
            .strat_defs
            .iter()
            .cloned()
            .enumerate()
            .map(|(source_index, mut def)| {
                def.origin = Some(pm.name.clone());
                def.source_index = Some(source_index);
                def.home = Some(pm.name.clone());
                def
            })
            .collect(),
    }
}

/// Inline statement variables shadowed by earlier imports as single-token colon variables at their
/// declared sort (`A` ↦ `A:List{X}`). Module-local aliases otherwise collide in the flattened grammar's
/// shared variable namespace, where [`Acc::add`] retains the first declaration. Only colliding variables
/// are inlined; non-colliding names remain bare and declarations remain available to commands.
fn inline_shadowed_vars(d: &mut FlatDecls, prior: &Acc, i: &mut Interner) {
    let mut declared: HashMap<&str, &str> = HashMap::new();
    for v in &prior.vars {
        for n in &v.names {
            declared.entry(n.as_str()).or_insert(v.sort.as_str());
        }
    }
    let mut var_inline: HashMap<String, String> = HashMap::new();
    for v in &d.vars {
        for n in &v.names {
            if declared
                .get(n.as_str())
                .is_some_and(|s| *s != v.sort.as_str())
            {
                var_inline.insert(n.clone(), v.sort.clone()); // this module's var loses the name-dedup
            }
        }
    }
    if var_inline.is_empty() {
        return;
    }
    for st in &mut d.statements {
        inline_statement_vars(st, &var_inline, i);
    }
}

/// Rewrite every bare occurrence of a `var_inline` name in a statement's term bubbles as a single-token
/// colon variable at its mapped sort (`A` ↦ `A:Bool`). A membership's sort is not a term bubble.
fn inline_statement_vars(st: &mut Statement, var_inline: &VarScope, i: &mut Interner) {
    let (no_bindings, no_ops) = (HashMap::new(), HashMap::new());
    let go = |b: &[Token], i: &mut Interner| subst_bubble(b, &no_bindings, &no_ops, var_inline, i);
    match st {
        Statement::Eq { lhs, rhs, cond, .. } | Statement::Rule { lhs, rhs, cond, .. } => {
            *lhs = go(lhs, i);
            *rhs = go(rhs, i);
            if let Some(c) = cond {
                *c = go(c, i);
            }
        }
        Statement::Mb { lhs, cond, .. } => {
            *lhs = go(lhs, i);
            if let Some(c) = cond {
                *c = go(c, i);
            }
        }
    }
}

/// [`inline_statement_vars`] for a strategy definition: its call-pattern parameters, every term bubble of
/// its body (including application-substitution variables, so `L[X <- t]` keeps naming the inlined rule
/// variable of a co-donated rule), and its condition, so one name keeps one spelling in the definition.
fn inline_strat_def_vars(
    def: &mut tnk_frontend::surface::ast::StratDef,
    var_inline: &VarScope,
    i: &mut Interner,
) {
    let (no_bindings, no_ops) = (HashMap::new(), HashMap::new());
    for param in &mut def.params {
        *param = subst_bubble(param, &no_bindings, &no_ops, var_inline, i);
    }
    rewrite_strategy_bubbles(&mut def.body, &mut |bubble| {
        subst_bubble(bubble, &no_bindings, &no_ops, var_inline, i)
    });
    if let Some(cond) = &mut def.cond {
        *cond = subst_bubble(cond, &no_bindings, &no_ops, var_inline, i);
    }
}

/// The variable table of the flattened module `root`, whose import closure (the root included) declared
/// `vars` (name-deduplicated, first declaration first) and `ops`. Imported variable aliases participate
/// only when no visible nullary operator redeclares the token; the root's own declarations are then
/// restored authoritatively.
fn root_var_table(
    mut vars: Vec<VarDecl>,
    ops: &[OpDecl],
    root: &PreModule,
    interner: &Interner,
) -> Vec<VarDecl> {
    let own_var_names: HashSet<&str> = root
        .vars
        .iter()
        .flat_map(|v| v.names.iter().map(String::as_str))
        .collect();
    let constant_names: HashSet<String> = ops
        .iter()
        .filter(|op| op.domain.is_empty())
        .map(|op| {
            op.name
                .iter()
                .map(|token| interner.resolve(token.sym))
                .collect()
        })
        .collect();
    for vd in &mut vars {
        vd.names.retain(|name| {
            !own_var_names.contains(name.as_str()) && !constant_names.contains(name)
        });
    }
    vars.retain(|vd| !vd.names.is_empty());
    vars.extend(root.vars.iter().cloned());
    vars
}

/// A variable table as a scope: each declared name mapped to its sort.
fn var_scope(vars: Vec<VarDecl>) -> VarScope {
    let mut scope = VarScope::new();
    for v in vars {
        for name in v.names {
            scope.entry(name).or_insert_with(|| v.sort.clone());
        }
    }
    scope
}

/// A home module's grammar variable table, the scope its own statements are parsed in: the aliases its
/// flattened grammar declares ([`root_var_table`]: imports included, imported names that a visible
/// constant redeclares left out, its own declarations authoritative). Only declarations are read, so the
/// home's closure is collected without donation scopes. A home that does not flatten falls back to its
/// own declarations.
fn home_var_scope(home: &str, db: &ModuleDb, views: &ViewDb, i: &mut Interner) -> VarScope {
    let Some(module) = db.get(home) else {
        return VarScope::new();
    };
    let mut acc = Acc::default();
    let vars = match collect_named(home, db, views, &mut acc, &mut HashSet::new(), i) {
        Ok(()) => root_var_table(acc.vars, &acc.ops, module, i),
        Err(_) => module.vars.clone(),
    };
    var_scope(vars)
}

/// Keep home-less renamed and parameter-copy donations independent of the flattened module's variable
/// table. Their bubbles parse against the flattened grammar, whose bare variables are the importer's own
/// declarations plus the first-donated imported alias of each name, so a bare variable there can change
/// sort or stop parsing. Each statement or strategy definition carrying a source scope gets the names that
/// the flattened variable table binds differently (at another sort, or not at all) inlined as single-token
/// colon variables at their source sort, the [`instantiate_decls`] technique. Names the flattened table
/// binds identically stay bare, keeping their spelling.
fn inline_rebound_vars(d: &mut FlatDecls, scopes: &DonationScopes, i: &mut Interner) {
    if scopes
        .statements
        .iter()
        .chain(&scopes.strat_defs)
        .all(Option::is_none)
    {
        return;
    }
    let mut flat_vars: HashMap<&str, &str> = HashMap::new();
    for v in &d.vars {
        for name in &v.names {
            flat_vars.entry(name.as_str()).or_insert(v.sort.as_str());
        }
    }
    let mut rebound: HashMap<*const VarScope, Rc<VarScope>> = HashMap::new();
    let mut rebound_of = |scope: &Rc<VarScope>| -> Rc<VarScope> {
        rebound
            .entry(Rc::as_ptr(scope))
            .or_insert_with(|| {
                Rc::new(
                    scope
                        .iter()
                        .filter(|(name, sort)| flat_vars.get(name.as_str()) != Some(&sort.as_str()))
                        .map(|(name, sort)| (name.clone(), sort.clone()))
                        .collect(),
                )
            })
            .clone()
    };
    let statement_inlines: Vec<Option<Rc<VarScope>>> = scopes
        .statements
        .iter()
        .map(|scope| scope.as_ref().map(&mut rebound_of))
        .collect();
    let def_inlines: Vec<Option<Rc<VarScope>>> = scopes
        .strat_defs
        .iter()
        .map(|scope| scope.as_ref().map(&mut rebound_of))
        .collect();
    for (st, inline) in d.statements.iter_mut().zip(statement_inlines) {
        if let Some(inline) = inline.filter(|inline| !inline.is_empty()) {
            inline_statement_vars(st, &inline, i);
        }
    }
    for (def, inline) in d.strat_defs.iter_mut().zip(def_inlines) {
        if let Some(inline) = inline.filter(|inline| !inline.is_empty()) {
            inline_strat_def_vars(def, &inline, i);
        }
    }
}

/// Flatten module `name`'s import closure into one combined [`PreModule`] named `name` (empty imports).
/// `views` resolves any parameterized instantiation `M{V}` reached in the closure.
pub fn flatten(
    name: &str,
    db: &ModuleDb,
    views: &ViewDb,
    interner: &mut Interner,
) -> Result<PreModule, String> {
    flatten_with_homes(name, db, views, interner).map(|(pm, _)| pm)
}

/// Like [`flatten`], but also return the per-statement **home** module names, parallel to the returned
/// module's `statements`. Imported statements can be parsed against their defining grammar through
/// [`crate::load::flatten_and_build`] and
/// [`tnk_frontend::load::build_loaded_module_homed`]. Named root statements carry `Some(root_name)`,
/// which the loader treats as self; `None` marks transient roots or donations without a distinct home and
/// uses the flattened grammar.
pub fn flatten_with_homes(
    name: &str,
    db: &ModuleDb,
    views: &ViewDb,
    interner: &mut Interner,
) -> Result<(PreModule, Vec<Option<String>>), String> {
    let mut acc = Acc::tracking_scopes();
    let mut visited = HashSet::new();
    collect_named(name, db, views, &mut acc, &mut visited, interner)?;
    // The flattened module is the root module with its imports inlined, so it keeps the root's kind
    // (`mod` stays a system module — its rules survive flattening) and its theory flag.
    let root = db.get(name);
    // Root statements precede imported statements; imports donate post-order, deepest first. Move the
    // root-owned block to the front while preserving declaration order and rotating home tags and
    // object-module provenance in lockstep.
    if let Some(pm) = root {
        acc.statements.rotate_right(pm.statements.len());
        acc.statement_homes.rotate_right(pm.statements.len());
        acc.object_statements.rotate_right(pm.statements.len());
        acc.scopes.statements.rotate_right(pm.statements.len());
        acc.strat_decls.rotate_right(pm.strat_decls.len());
        acc.strat_defs.rotate_right(pm.strat_defs.len());
        acc.scopes.strat_defs.rotate_right(pm.strat_defs.len());
    }
    let (kind, is_theory, is_strategy, is_object) = root
        .map(|pm| (pm.kind, pm.is_theory, pm.is_strategy, pm.is_object))
        .unwrap_or((ModuleKind::Functional, false, false, false));
    let homes = std::mem::take(&mut acc.statement_homes);
    let scopes = std::mem::take(&mut acc.scopes);
    let mut d = acc.into_decls();
    // Imported variable aliases participate only when no visible nullary operator redeclares the token.
    // Root-owned variables are then restored authoritatively.
    if let Some(pm) = root {
        d.vars = root_var_table(std::mem::take(&mut d.vars), &d.ops, pm, interner);
    }
    debug_assert_eq!(
        homes.len(),
        d.statements.len(),
        "statement_homes parallel to statements"
    );
    // The variable table is now final: keep renamed and parameter-copy statements on their source scope.
    inline_rebound_vars(&mut d, &scopes, interner);
    let pm = PreModule {
        name: name.to_string(),
        source_line: root.and_then(|module| module.source_line),
        diagnostics: root
            .map(|module| module.diagnostics.clone())
            .unwrap_or_default(),
        kind,
        is_theory,
        is_strategy,
        // The flattened module keeps the root's object-orientation, so `load_statements` runs the
        // object-pattern completion on its (own + imported) statements when the root is an `omod`.
        is_object,
        // Under any root, a statement declared by an object module is completed: importing an `omod`
        // into a `mod` keeps the meaning of the omod's statements.
        object_statements: d.object_statements,
        // The flattened module is fully resolved: each parameter's copy (its `X$s` sorts) is inlined, so
        // no formal parameters remain.
        params: Vec::new(),
        imports: Vec::new(),
        sorts: d.sorts,
        subsorts: d.subsorts,
        ops: d.ops,
        vars: d.vars,
        statements: d.statements,
        strat_decls: d.strat_decls,
        strat_defs: d.strat_defs,
    };
    Ok((pm, homes))
}

/// Flatten a **transient** module given directly as a [`PreModule`] (not registered in `db`) — its
/// imports are still resolved from `db`. Used by META-LEVEL descent to build the object module of a
/// meta-module term (`metaReduce`'s first argument), e.g. `[Q]` = `sth Q is including Q . … endsth`. The
/// transient's own name is replaced by a fixed sentinel so that a `including Q .` of a same-named DB
/// module resolves to that DB module rather than being deduped against the transient itself.
pub fn flatten_pre(
    pm: &PreModule,
    db: &ModuleDb,
    views: &ViewDb,
    interner: &mut Interner,
) -> Result<PreModule, String> {
    const SENTINEL: &str = "%META-DOWN%";
    let mut acc = Acc::tracking_scopes();
    let mut visited = HashSet::new();
    visited.insert(SENTINEL.to_string());
    let params: Vec<(String, String)> = pm
        .params
        .iter()
        .map(|p| (p.name.clone(), p.theory.clone()))
        .collect();
    for (param, theory) in &params {
        add_parameter_copy(param, theory, db, views, &mut acc, interner)?;
    }
    let scope: Vec<String> = params.iter().map(|(n, _)| n.clone()).collect();
    for imp in &pm.imports {
        if !pm.is_strategy && import_targets_strategy(&imp.expr, db) {
            continue;
        }
        collect_expr(
            &imp.expr,
            db,
            views,
            &mut acc,
            &mut visited,
            interner,
            &scope,
        )?;
    }
    let mut own = own_decls(pm);
    inline_shadowed_vars(&mut own, &acc, interner);
    // Transient statements parse against the flattened, down-translated grammar, so they have no distinct
    // statement home. Rotate them ahead of imported statements because the transient is the root module.
    acc.add(own, None);
    acc.statements.rotate_right(pm.statements.len());
    acc.statement_homes.rotate_right(pm.statements.len());
    acc.object_statements.rotate_right(pm.statements.len());
    acc.scopes.statements.rotate_right(pm.statements.len());
    acc.strat_decls.rotate_right(pm.strat_decls.len());
    acc.strat_defs.rotate_right(pm.strat_defs.len());
    acc.scopes.strat_defs.rotate_right(pm.strat_defs.len());
    let scopes = std::mem::take(&mut acc.scopes);
    let mut d = acc.into_decls();
    inline_rebound_vars(&mut d, &scopes, interner);
    Ok(PreModule {
        name: SENTINEL.to_string(),
        source_line: pm.source_line,
        diagnostics: pm.diagnostics.clone(),
        kind: pm.kind,
        is_theory: pm.is_theory,
        is_strategy: pm.is_strategy,
        is_object: pm.is_object,
        object_statements: d.object_statements,
        params: Vec::new(),
        imports: Vec::new(),
        sorts: d.sorts,
        subsorts: d.subsorts,
        ops: d.ops,
        vars: d.vars,
        statements: d.statements,
        strat_decls: d.strat_decls,
        strat_defs: d.strat_defs,
    })
}

/// The base module/theory names in *module position* of an import expression (a plain name, a sum's sides,
/// a renaming's inner, an instantiation's base — an instantiation's `{…}` *arguments* are views, not
/// imported modules, so they are excluded). Used by the import-hygiene checks below.
fn import_module_bases<'a>(expr: &'a ModuleExpr, out: &mut Vec<&'a str>) {
    match expr {
        ModuleExpr::Named(n) => out.push(n),
        ModuleExpr::Sum(a, b) => {
            import_module_bases(a, out);
            import_module_bases(b, out);
        }
        ModuleExpr::Rename(inner, _) => import_module_bases(inner, out),
        ModuleExpr::Instantiation(base, _) => import_module_bases(base, out),
    }
}

/// Whether a module-position import targets a theory. A plain module ignores theory imports.
fn import_targets_theory(expr: &ModuleExpr, db: &ModuleDb) -> bool {
    let mut bases = Vec::new();
    import_module_bases(expr, &mut bases);
    bases.iter().any(|n| db.get(n).is_some_and(|m| m.is_theory))
}

/// Strategy declarations and definitions are donated only into strategy modules and theories.
fn import_targets_strategy(expr: &ModuleExpr, db: &ModuleDb) -> bool {
    let mut bases = Vec::new();
    import_module_bases(expr, &mut bases);
    bases
        .iter()
        .any(|name| db.get(name).is_some_and(|module| module.is_strategy))
}

/// Whether an import expression directly names the importing module `name` (a self-import).
fn import_names_self(expr: &ModuleExpr, name: &str) -> bool {
    let mut bases = Vec::new();
    import_module_bases(expr, &mut bases);
    bases.contains(&name)
}

/// Whether the base of a module expression is a theory (`fth`/`th`) — the target of a view is a theory iff
/// instantiating with that view leaves the parameter free.
fn expr_base_is_theory(e: &ModuleExpr, db: &ModuleDb) -> bool {
    match e {
        ModuleExpr::Named(n) => db.get(n).is_some_and(|m| m.is_theory),
        ModuleExpr::Instantiation(base, _) => expr_base_is_theory(base, db),
        ModuleExpr::Rename(inner, _) => expr_base_is_theory(inner, db),
        ModuleExpr::Sum(a, _) => expr_base_is_theory(a, db),
    }
}

/// Whether an instantiation argument leaves its parameter free: a **theory-view** (its `to` target is a
/// theory) does; a **module-view** grounds it; a **by-parameter** argument (an enclosing parameter, in
/// `scope`) is free but legitimately bound by the importer's own parameter.
fn arg_leaves_free_param(
    arg: &ModuleExpr,
    db: &ModuleDb,
    views: &ViewDb,
    scope: &[String],
) -> bool {
    match arg {
        ModuleExpr::Named(p) if scope.iter().any(|n| n == p) => false, // by-parameter (bound by importer)
        ModuleExpr::Named(v) => views
            .get(v)
            .is_some_and(|view| expr_base_is_theory(&view.to, db)),
        ModuleExpr::Instantiation(base, _) => match &**base {
            ModuleExpr::Named(v) => views
                .get(v)
                .is_some_and(|view| expr_base_is_theory(&view.to, db)),
            _ => false,
        },
        _ => false,
    }
}

/// Whether importing an instantiation leaves a free parameter. Only the final argument layer can ground
/// a chain; a renamed expression without an instantiation chain is not gated here.
fn import_leaves_free_param(
    expr: &ModuleExpr,
    db: &ModuleDb,
    views: &ViewDb,
    scope: &[String],
) -> bool {
    let Some((_, arg_lists)) = unchain(expr) else {
        return false;
    };
    let Some(last) = arg_lists.last() else {
        return false;
    };
    last.iter()
        .any(|a| arg_leaves_free_param(a, db, views, scope))
}

fn collect_named(
    name: &str,
    db: &ModuleDb,
    views: &ViewDb,
    acc: &mut Acc,
    visited: &mut HashSet<String>,
    interner: &mut Interner,
) -> Result<(), String> {
    if !visited.insert(name.to_string()) {
        return Ok(()); // already merged (diamond)
    }
    let pm = db
        .get(name)
        .ok_or_else(|| format!("imported module `{name}` is not defined"))?;
    // Parameter copies first (a parameter `X :: T` behaves like an import of a renamed `T`), then the
    // regular imports, then the module's own declarations.
    let params: Vec<(String, String)> = pm
        .params
        .iter()
        .map(|p| (p.name.clone(), p.theory.clone()))
        .collect();
    for (param, theory) in &params {
        add_parameter_copy(param, theory, db, views, acc, interner)?;
    }
    // The module's own parameters are in scope for its imports: an import `LIST{X}` of a parameter `X`
    // is a *by-parameter* instantiation — `X` is not a view. Standalone (here) its
    // parameters stay free, so the imports are collected unsubstituted with `X` in scope.
    let scope: Vec<String> = params.iter().map(|(n, _)| n.clone()).collect();
    for imp in &pm.imports {
        // Self-imports are mutually recursive and make the module unusable.
        if import_names_self(&imp.expr, name) {
            return Err(format!(
                "mutually recursive import of module `{name}` ignored"
            ));
        }
        if !pm.is_strategy && import_targets_strategy(&imp.expr, db) {
            continue;
        }
        // Plain modules ignore theory imports. The reverse direction and parameter bounds remain valid.
        if !pm.is_theory && import_targets_theory(&imp.expr, db) {
            continue;
        }
        // Importing an instance with a parameter left free makes the importer unusable.
        if import_leaves_free_param(&imp.expr, db, views, &scope) {
            return Err(format!(
                "cannot import module `{}` because it has free parameters",
                canonical_key(&imp.expr)
            ));
        }
        collect_expr(&imp.expr, db, views, acc, visited, interner, &scope)?;
    }
    let pm = db.get(name).expect("present");
    let mut own = own_decls(pm);
    inline_shadowed_vars(&mut own, acc, interner);
    // Append own declarations after imports. Statements from a plain named module retain `name` as their
    // home so the loader can reparse them when the flattened grammar is ambiguous.
    acc.add(own, Some(name));
    Ok(())
}

/// Add a parameter copy of `theory` under `param`: flatten the theory and qualify each theory-owned sort
/// `s` as `param$s`. Imported module sorts keep their shared names. The fresh scope is independent of any
/// unrenamed import of the same theory.
fn add_parameter_copy(
    param: &str,
    theory: &str,
    db: &ModuleDb,
    views: &ViewDb,
    acc: &mut Acc,
    interner: &mut Interner,
) -> Result<(), String> {
    let mut tmp = acc.bundle();
    let mut tmp_visited = HashSet::new();
    collect_named(theory, db, views, &mut tmp, &mut tmp_visited, interner)?;
    let scopes = tmp.donation_scopes(Some(theory), db, views, interner);
    let decls = tmp.into_decls();
    // The theory's genuine sorts (theory-declared, excluding module-origin) — the ones renamed to `X$s`.
    let param_sorts = theory_param_sorts(theory, db, views, interner)?;
    let mut items: Vec<RenameItem> = decls
        .sorts
        .iter()
        .filter(|s| param_sorts.contains(s.as_str()))
        .map(|s| RenameItem::Sort {
            from: s.clone(),
            to: format!("{param}${s}"),
        })
        .collect();
    // A parameter constant `op c : … [pconst]` is prefixed like a parameter sort: `c ↦ X$c` (the body
    // refers to it as `X$c`, and instantiation maps `X$c` through the view's op map for `c`).
    for op in &decls.ops {
        if op.attrs.pconst {
            let name: String = op.name.iter().map(|t| interner.resolve(t.sym)).collect();
            items.push(RenameItem::Op {
                from: name.clone(),
                to: format!("{param}${name}"),
                dom_range: None,
                attrs: Attrs::default(),
            });
        }
    }
    let (renamed, scopes) = rename_bundle(decls, scopes, &items, interner)?;
    // Parameter-copy statements are rewritten for the flattened grammar and therefore have no distinct
    // statement home; only plain named imports retain homes. Their source variable scopes travel along so
    // the importer's variables cannot re-bind them.
    acc.add_scoped(renamed, None, scopes);
    Ok(())
}

/// The set of a parameter theory's own sorts — theory-declared sorts, excluding those inherited from an
/// imported *module* ([`module_origin_sorts`]). These are exactly the `s` renamed to `param$s` by
/// [`add_parameter_copy`]; equivalently, the `s` for which `X$s` is a genuine parameter sort. Any other
/// `X$…` occurrence in a parameterized module's body is a "fake" parameter sort.
fn theory_param_sorts(
    theory: &str,
    db: &ModuleDb,
    views: &ViewDb,
    interner: &mut Interner,
) -> Result<HashSet<String>, String> {
    let mut tmp = Acc::default();
    let mut tmp_visited = HashSet::new();
    collect_named(theory, db, views, &mut tmp, &mut tmp_visited, interner)?;
    let sorts = tmp.into_decls().sorts;
    let mut module_sorts = HashSet::new();
    module_origin_sorts(
        theory,
        db,
        views,
        interner,
        &mut HashSet::new(),
        &mut module_sorts,
    )?;
    Ok(sorts
        .into_iter()
        .filter(|s| !module_sorts.contains(s))
        .collect())
}

/// The canonical names of a theory's **parameter constants** (`op c : … [pconst]`) — the constants a
/// parameterized module refers to as `X$c` and that instantiation maps through the view's op map for `c`.
fn theory_pconst_ops(
    theory: &str,
    db: &ModuleDb,
    views: &ViewDb,
    interner: &mut Interner,
) -> Result<HashSet<String>, String> {
    let mut tmp = Acc::default();
    let mut tmp_visited = HashSet::new();
    collect_named(theory, db, views, &mut tmp, &mut tmp_visited, interner)?;
    Ok(tmp
        .into_decls()
        .ops
        .iter()
        .filter(|op| op.attrs.pconst)
        .map(|op| op.name.iter().map(|t| interner.resolve(t.sym)).collect())
        .collect())
}

fn collect_expression_sorts(
    expr: &ModuleExpr,
    db: &ModuleDb,
    views: &ViewDb,
    interner: &mut Interner,
    out: &mut HashSet<String>,
) -> Result<(), String> {
    let mut acc = Acc::default();
    let mut visited = HashSet::new();
    collect_expr(expr, db, views, &mut acc, &mut visited, interner, &[])?;
    out.extend(acc.into_decls().sorts);
    Ok(())
}

/// Collect only the module-origin subset of one theory import expression. Sums are classified branch by
/// branch so a legal `MODULE + THEORY` import does not turn the theory's own sorts into module sorts.
/// Renamings are then applied to that subset; instantiating a parameterized module contributes the whole
/// instantiated signature because every sort in that result is module-origin.
#[allow(clippy::too_many_arguments)]
fn module_origin_expr_sorts(
    expr: &ModuleExpr,
    db: &ModuleDb,
    views: &ViewDb,
    interner: &mut Interner,
    seen: &mut HashSet<String>,
    out: &mut HashSet<String>,
) -> Result<(), String> {
    match expr {
        ModuleExpr::Named(name) => match db.get(name) {
            Some(module) if module.is_theory => {
                module_origin_sorts(name, db, views, interner, seen, out)
            }
            Some(_) => collect_expression_sorts(expr, db, views, interner, out),
            None => Ok(()),
        },
        ModuleExpr::Sum(left, right) => {
            module_origin_expr_sorts(left, db, views, interner, seen, out)?;
            module_origin_expr_sorts(right, db, views, interner, seen, out)
        }
        ModuleExpr::Rename(inner, items) => {
            let mut inner_sorts = HashSet::new();
            module_origin_expr_sorts(inner, db, views, interner, seen, &mut inner_sorts)?;
            let sort_maps: HashMap<&str, &str> = items
                .iter()
                .filter_map(|item| match item {
                    RenameItem::Sort { from, to } => Some((from.as_str(), to.as_str())),
                    _ => None,
                })
                .collect();
            for mut sort in inner_sorts {
                if let Some(target) = sort_maps.get(sort.as_str()) {
                    sort = (*target).to_string();
                }
                out.insert(sort);
            }
            Ok(())
        }
        ModuleExpr::Instantiation(base, _) => {
            let mut bases = Vec::new();
            import_module_bases(base, &mut bases);
            if bases
                .iter()
                .any(|name| db.get(name).is_some_and(|module| !module.is_theory))
            {
                collect_expression_sorts(expr, db, views, interner, out)
            } else {
                module_origin_expr_sorts(base, db, views, interner, seen, out)
            }
        }
    }
}

/// Collect the sorts a theory inherits from imported **modules** (vs. theories), recursively so an
/// imported theory contributes its own module-origin sorts. Each transformed import branch retains its
/// resulting sort names, while a mixed module/theory sum keeps the theory's own sorts parameter-owned.
fn module_origin_sorts(
    name: &str,
    db: &ModuleDb,
    views: &ViewDb,
    interner: &mut Interner,
    seen: &mut HashSet<String>,
    out: &mut HashSet<String>,
) -> Result<(), String> {
    if !seen.insert(name.to_string()) {
        return Ok(());
    }
    let result = (|| {
        let Some(pm) = db.get(name) else {
            return Ok(());
        };
        let imports: Vec<ModuleExpr> = pm.imports.iter().map(|imp| imp.expr.clone()).collect();
        for import in &imports {
            module_origin_expr_sorts(import, db, views, interner, seen, out)?;
        }
        Ok(())
    })();
    seen.remove(name);
    result
}

fn renames_free_parameter_sort(item: &RenameItem, scope: &[String]) -> bool {
    let RenameItem::Sort { from, .. } = item else {
        return false;
    };
    scope.iter().any(|parameter| {
        from.strip_prefix(parameter)
            .is_some_and(|rest| rest.starts_with('$'))
    })
}

fn collect_expr(
    expr: &ModuleExpr,
    db: &ModuleDb,
    views: &ViewDb,
    acc: &mut Acc,
    visited: &mut HashSet<String>,
    interner: &mut Interner,
    scope: &[String],
) -> Result<(), String> {
    match expr {
        ModuleExpr::Named(n) => collect_named(n, db, views, acc, visited, interner),
        ModuleExpr::Sum(a, b) => {
            collect_expr(a, db, views, acc, visited, interner, scope)?;
            collect_expr(b, db, views, acc, visited, interner, scope)
        }
        ModuleExpr::Rename(inner, items) => {
            // `A * (R)` is a distinct module from `A`: key it by its canonical form so it merges once,
            // and flatten `inner` in a fresh scope (the renamed content is independent of the unrenamed).
            if !visited.insert(canonical_key(expr)) {
                return Ok(());
            }
            let mut tmp = acc.bundle();
            let mut tmp_visited = HashSet::new();
            collect_expr(
                inner,
                db,
                views,
                &mut tmp,
                &mut tmp_visited,
                interner,
                scope,
            )?;
            let root = match &**inner {
                ModuleExpr::Named(name) => Some(name.as_str()),
                _ => None,
            };
            let scopes = tmp.donation_scopes(root, db, views, interner);
            let (renamed, scopes) = if items
                .iter()
                .any(|item| renames_free_parameter_sort(item, scope))
            {
                // An enclosing parameter owns its qualified sorts, so import renaming does not rename them.
                let effective: Vec<_> = items
                    .iter()
                    .filter(|item| !renames_free_parameter_sort(item, scope))
                    .cloned()
                    .collect();
                rename_bundle(tmp.into_decls(), scopes, &effective, interner)?
            } else {
                rename_bundle(tmp.into_decls(), scopes, items, interner)?
            };
            // Renamed donation: bubbles are rewritten in-place and parse against the flattened grammar,
            // unlike plain named imports. Their source variable scopes travel along so the importer's
            // variables cannot re-bind them.
            acc.add_scoped(renamed, None, scopes);
            Ok(())
        }
        ModuleExpr::Instantiation(base, args) => {
            // `M{A, …}` (or a chain `M{A}{B}`) merges once, keyed by its canonical instance name.
            if !visited.insert(canonical_key(expr)) {
                return Ok(());
            }
            // For an instantiated renamed module `(M * R){V}`, instantiate the inner module first, then
            // apply `R` to module-level sorts and operators. Parameter-theory sort mappings are no-ops
            // after substitution.
            if let ModuleExpr::Rename(inner, items) = &**base {
                let mut tmp = acc.bundle();
                let mut tmp_visited = HashSet::new();
                let inst = ModuleExpr::Instantiation(inner.clone(), args.clone());
                collect_expr(
                    &inst,
                    db,
                    views,
                    &mut tmp,
                    &mut tmp_visited,
                    interner,
                    scope,
                )?;
                // Rename items use the inner module's parameter names while instance sorts use argument
                // names. Substitute parameters positionally before matching structured names.
                let items = subst_rename_item_params(inner, args, db, items);
                let scopes = tmp.donation_scopes(None, db, views, interner);
                let (renamed, scopes) = rename_bundle(tmp.into_decls(), scopes, &items, interner)?;
                acc.add_scoped(renamed, None, scopes);
                return Ok(());
            }
            let (mname, arg_lists) = unchain(expr)
                .ok_or("the base of an instantiation must be a named module, not a sum")?;
            instantiate(mname, &arg_lists, db, views, acc, visited, interner, scope)
        }
    }
}

/// Flatten an instantiation expression (possibly a chain `M{A}{B}`) into the base module name and the
/// argument lists, **outermost last**: `M{A}{B}` ⇒ `(M, [[A], [B]])`. `None` if the base is not a chain of
/// instantiations rooted at a named module.
fn unchain(expr: &ModuleExpr) -> Option<(&str, Vec<&[ModuleExpr]>)> {
    match expr {
        ModuleExpr::Instantiation(base, args) => match &**base {
            ModuleExpr::Named(m) => Some((m, vec![args.as_slice()])),
            ModuleExpr::Instantiation(..) => {
                let (m, mut lists) = unchain(base)?;
                lists.push(args.as_slice());
                Some((m, lists))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Substitute an instantiation's parameter names into a renaming's structured sort names,
/// positionally (`Array{X,Y}` over `ARRAY{X :: TRIV, Y :: TRIV}` instantiated `{Nat, Int0}` →
/// `Array{Nat,Int0}`; the `to` side likewise, `Vector{Y}` → `Vector{Int0}`), so the rename items
/// match the instance's sort spellings. A kind spelling in a sort position substitutes each component
/// (`[List{X}]` → `[List{Nat}]`). Non-structured names and op items pass through (an op rename's
/// from/to get the same brace-argument treatment).
fn subst_rename_item_params(
    inner: &ModuleExpr,
    args: &[ModuleExpr],
    db: &ModuleDb,
    items: &[RenameItem],
) -> Vec<RenameItem> {
    let ModuleExpr::Named(mname) = inner else {
        return items.to_vec();
    };
    let Some(pm) = db.get(mname) else {
        return items.to_vec();
    };
    let map: HashMap<&str, String> = pm
        .params
        .iter()
        .zip(args)
        .map(|(p, a)| (p.name.as_str(), canonical_key(a)))
        .collect();
    let subst = |name: &str| subst_brace_args(name, &map);
    let subst_sort = |name: &str| match kind_components(name) {
        Some(components) => {
            let substituted: Vec<String> = components.iter().map(|c| subst(c)).collect();
            format!("[{}]", substituted.join(","))
        }
        None => subst(name),
    };
    items
        .iter()
        .map(|it| match it {
            RenameItem::Sort { from, to } => RenameItem::Sort {
                from: subst_sort(from),
                to: subst_sort(to),
            },
            RenameItem::Op {
                from,
                to,
                attrs,
                dom_range,
                ..
            } => RenameItem::Op {
                from: subst(from),
                to: subst(to),
                attrs: attrs.clone(),
                dom_range: dom_range
                    .as_ref()
                    .map(|(d, r)| (d.iter().map(|s| subst_sort(s)).collect(), subst_sort(r))),
            },
            other => other.clone(),
        })
        .collect()
}

/// Rewrite each top-level brace argument of a structured name through `map` (depth-aware; nested
/// structured arguments recurse): `Array{X,Y}` with `{X → Nat, Y → Int0}` → `Array{Nat,Int0}`.
fn subst_brace_args(name: &str, map: &HashMap<&str, String>) -> String {
    let Some(open) = name.find('{') else {
        return map.get(name).cloned().unwrap_or_else(|| name.to_string());
    };
    if !name.ends_with('}') {
        return name.to_string();
    }
    let base = &name[..open];
    let inner = &name[open + 1..name.len() - 1];
    let mut out_args: Vec<String> = Vec::new();
    let mut depth = 0i32;
    let mut start = 0usize;
    for (idx, c) in inner.char_indices() {
        match c {
            '{' | '[' => depth += 1,
            '}' | ']' => depth -= 1,
            ',' if depth == 0 => {
                out_args.push(subst_brace_args(inner[start..idx].trim(), map));
                start = idx + 1;
            }
            _ => {}
        }
    }
    out_args.push(subst_brace_args(inner[start..].trim(), map));
    format!("{base}{{{}}}", out_args.join(","))
}

/// Instantiate the parameterized module `mname` with the argument-list chain `arg_lists` (one list per
/// `{…}` in a chain `M{A}{B}`, outermost last), against the enclosing parameter `scope`. Each parameter's
/// arguments across the chain are *composed* ([`resolve_arg`] per level): a module-view (kind 3) imports its
/// target and binds the parameter to its sort image, a by-parameter argument (kind 2) prefix-renames
/// `X$s ↦ p$s`, and a theory-view (kind 1) leaves the parameter free for the next level to bind — so a
/// chain `BOX{ToT2}{C2}` composes the theory-view `ToT2` with the module-view `C2` into one binding
/// (`X$Elt ↦ Hue`, `Box{X} ↦ Box{ToT2}{C2}`). `mname`'s imports are re-instantiated with the bound
/// parameters substituted in, and its own declarations merged under the binding (with variables inlined as
/// colon variables at their instantiated sorts).
#[allow(clippy::too_many_arguments)]
fn instantiate(
    mname: &str,
    arg_lists: &[&[ModuleExpr]],
    db: &ModuleDb,
    views: &ViewDb,
    acc: &mut Acc,
    visited: &mut HashSet<String>,
    interner: &mut Interner,
    scope: &[String],
) -> Result<(), String> {
    let pm = db
        .get(mname)
        .ok_or_else(|| format!("instantiated module `{mname}` is not defined"))?;
    let nparams = pm.params.len();
    for lvl in arg_lists {
        if lvl.len() != nparams {
            return Err(format!(
                "instantiation `{mname}{{…}}` has {} argument(s) but `{mname}` has {nparams} parameter(s)",
                lvl.len()
            ));
        }
    }

    // For each parameter, resolve and compose its chain of arguments. Only the *last* level's target is
    // imported (an earlier theory-view's target is a theory, contributing only a sort/op mapping); the
    // sort images compose left-to-right; the structured-sort name is the whole chain (`ToT2}{C2`).
    let mut bindings: HashMap<String, ParamBinding> = HashMap::new();
    let mut op_subst: HashMap<String, Vec<Token>> = HashMap::new();
    let mut op_recon: Vec<ViewOpMap> = Vec::new();
    let mut param_to_arg: HashMap<String, ModuleExpr> = HashMap::new();
    for (i, param) in pm.params.iter().enumerate() {
        let chain: Vec<&ModuleExpr> = arg_lists.iter().map(|lvl| &lvl[i]).collect();
        let resolutions: Vec<ArgResolution> = chain
            .iter()
            .map(|a| resolve_arg(a, views, db, interner, scope))
            .collect::<Result<_, _>>()
            .map_err(|e| format!("instantiation `{mname}{{…}}`: {e}"))?;
        // Import the grounding (last) target; compose op maps across the chain.
        let last = resolutions.last().expect("at least one level");
        if let Some(target) = &last.target {
            collect_expr(target, db, views, acc, visited, interner, scope)?;
        }
        // A theory's parameter constants `c` (`[pconst]`) appear in the body as `X$c` (like a parameter
        // sort `X$s`), so the view's op map for `c` keys the substitution under `param.name$c`.
        // Exact source profiles are written in the theory's unqualified sort names. The standalone source
        // grammar contains the parameter copy, where genuine theory sorts are named `X$s`; module-origin
        // sorts retain their names.
        let theory_sorts = theory_param_sorts(&param.theory, db, views, interner)?;
        let pconst_ops = theory_pconst_ops(&param.theory, db, views, interner)?;
        for r in &resolutions {
            for (k, val) in &r.op_subst {
                if pconst_ops.contains(k) {
                    op_subst.insert(format!("{}${}", param.name, k), val.clone());
                } else {
                    op_subst.insert(k.clone(), val.clone());
                }
            }
            op_recon.extend(r.op_recon.iter().cloned().map(|mut map| {
                if pconst_ops.contains(&map.source) {
                    map.source = format!("{}${}", param.name, map.source);
                }
                if let Some((domain, range)) = &mut map.dom_range {
                    // A selector sort may be a kind spelling (`op f : [Elt] -> [Elt] to g`), whose
                    // theory-owned components are qualified one by one.
                    let qualify = |sort: &mut String| {
                        if let Some(qualified) = map_sort_spelling(sort, |component| {
                            theory_sorts
                                .contains(component)
                                .then(|| format!("{}${component}", param.name))
                        }) {
                            *sort = qualified;
                        }
                    };
                    for sort in domain {
                        qualify(sort);
                    }
                    qualify(range);
                }
                map
            }));
        }
        // Compose the sort image: each source sort threaded through every level's map in order.
        let mut sort_image: HashMap<String, String> = HashMap::new();
        let sources: HashSet<String> = resolutions
            .iter()
            .flat_map(|r| r.binding.sort_image.keys().cloned())
            .collect();
        for s in sources {
            let mut cur = s.clone();
            for r in &resolutions {
                cur = r.binding.sort_image.get(&cur).cloned().unwrap_or(cur);
            }
            sort_image.insert(s, cur);
        }
        let view_name = chain
            .iter()
            .map(|a| canonical_key(a))
            .collect::<Vec<_>>()
            .join("}{");
        // The parameter theory's genuine sorts — so a fake `X$Foo` in the body survives.
        bindings.insert(
            param.name.clone(),
            ParamBinding {
                view_name,
                // The by-parameter `$`-sort rename uses only the last level (the surviving parameter), not the
                // joined chain — so `LIST{ORD}{X}` renames `X$Elt ↦ X$Elt`, not `↦ ORD}{X$Elt`.
                final_name: last.binding.view_name.clone(),
                sort_image,
                by_param: last.binding.by_param,
                theory_sorts: Some(theory_sorts),
            },
        );
        // For re-instantiating `mname`'s imports that mention the parameter, the last level's argument is
        // the effective binding (an intervening theory-view changes only the theory, not the value).
        param_to_arg.insert(
            param.name.clone(),
            (**chain.last().expect("at least one level")).clone(),
        );
    }

    // `M`'s regular imports with the parameter substitution applied (a bound parameter `X` in an import
    // `LIST{X}` becomes its argument — `LIST{ToN}` for a view, `LIST{Y}` for an enclosing parameter), then
    // its own declarations under the binding. Deduped via `visited`.
    let imports: Vec<ModuleExpr> = pm
        .imports
        .iter()
        .map(|imp| subst_params_in_expr(&imp.expr, &param_to_arg, db))
        .collect();
    for imp in &imports {
        collect_expr(imp, db, views, acc, visited, interner, scope)?;
    }
    let pm = db.get(mname).expect("present");
    let mut decls = own_decls(pm);
    // Mixfix view op→op maps: rewrite the statement bubbles grammar-aware (fixity may change) *before* the
    // textual instantiation pass inlines variables/sorts. The remaining (prefix→prefix, op→term) maps ride
    // `op_subst` inside `instantiate_decls`.
    if !op_recon.is_empty() {
        apply_view_op_recon(&mut decls, mname, db, views, &op_recon, interner)?;
    }
    // Instantiated donation: variables/sorts inlined into the bubbles, so parse against the flattened
    // grammar; instantiated donations have no distinct source home.
    let instantiated = instantiate_decls(decls, &bindings, &op_subst, interner);
    acc.add(instantiated, None);
    Ok(())
}

/// Rewrite every raw term bubble nested in a strategy expression, preserving its combinator tree.
fn rewrite_strategy_bubbles(
    expr: &mut StratExpr,
    rewrite: &mut impl FnMut(&[Token]) -> Vec<Token>,
) {
    rewrite_strategy_bubbles_with(expr, &mut |bubble, _is_condition| rewrite(bubble));
}

/// [`rewrite_strategy_bubbles`], also telling `rewrite` whether a bubble is a `such that` condition
/// (`true`) rather than a term (`false`).
fn rewrite_strategy_bubbles_with(
    expr: &mut StratExpr,
    rewrite: &mut impl FnMut(&[Token], bool) -> Vec<Token>,
) {
    match expr {
        StratExpr::Idle | StratExpr::Fail | StratExpr::All => {}
        StratExpr::Apply {
            subst, substrats, ..
        } => {
            for (variable, value) in subst {
                *variable = rewrite(variable, false);
                *value = rewrite(value, false);
            }
            for child in substrats {
                rewrite_strategy_bubbles_with(child, rewrite);
            }
        }
        StratExpr::Top(child)
        | StratExpr::One(child)
        | StratExpr::Star(child)
        | StratExpr::Plus(child)
        | StratExpr::Normalize(child) => rewrite_strategy_bubbles_with(child, rewrite),
        StratExpr::Seq(left, right) | StratExpr::Union(left, right) => {
            rewrite_strategy_bubbles_with(left, rewrite);
            rewrite_strategy_bubbles_with(right, rewrite);
        }
        StratExpr::Branch {
            test,
            success,
            failure,
        } => {
            rewrite_strategy_bubbles_with(test, rewrite);
            rewrite_strategy_bubbles_with(success, rewrite);
            rewrite_strategy_bubbles_with(failure, rewrite);
        }
        StratExpr::Test { pattern, cond, .. } => {
            *pattern = rewrite(pattern, false);
            if let Some(cond) = cond {
                *cond = rewrite(cond, true);
            }
        }
        StratExpr::MatchRew {
            pattern,
            cond,
            subs,
            ..
        } => {
            *pattern = rewrite(pattern, false);
            if let Some(cond) = cond {
                *cond = rewrite(cond, true);
            }
            for (variable, child) in subs {
                *variable = rewrite(variable, false);
                rewrite_strategy_bubbles_with(child, rewrite);
            }
        }
        StratExpr::Sugar { args, .. } => {
            for child in args {
                rewrite_strategy_bubbles_with(child, rewrite);
            }
        }
        StratExpr::Call { args, .. } => {
            for arg in args {
                *arg = rewrite(arg, false);
            }
        }
    }
}

/// Rewrite `d`'s statement bubbles for a view's mixfix op→op maps `op_recon` (source canonical → target
/// canonical): build the source (parameterized) module `mname`'s grammar (flattened standalone, so the
/// parameter-theory operators and the module's variables are in scope) and re-emit each mapped operator
/// application in the target operator's syntax ([`ViewOpSubst`]). Runs on the *source* bubbles (bare
/// variables, source ops), so the subsequent [`instantiate_decls`] pass still inlines variables/sorts and
/// applies the textual `op_subst`. Statement, strategy-definition, and `such that` conditions are rewritten
/// term by term ([`ViewOpSubst::rewrite_condition`]).
fn apply_view_op_recon(
    d: &mut FlatDecls,
    mname: &str,
    db: &ModuleDb,
    views: &ViewDb,
    op_recon: &[ViewOpMap],
    interner: &mut Interner,
) -> Result<(), String> {
    let mut src = flatten(mname, db, views, interner)?;
    // `flatten` de-duplicates variable *names* keeping the first (import) declaration, so a body variable
    // that collides with an imported one (e.g. `A B : X$Elt` vs BOOL's `A B C : Bool`) is shadowed at the
    // wrong sort in the source grammar, and a bubble like `lt(A, B)` fails to parse. The module's own
    // variables must win here: drop every source declaration of an own-variable name, then re-add the own
    // declarations authoritatively.
    let own_var_names: HashSet<String> = d
        .vars
        .iter()
        .flat_map(|v| v.names.iter().cloned())
        .collect();
    for vd in &mut src.vars {
        vd.names.retain(|n| !own_var_names.contains(n));
    }
    src.vars.retain(|vd| !vd.names.is_empty());
    src.vars.extend(d.vars.iter().cloned());
    let Some(mapper) = ViewOpSubst::new(&src, op_recon, ProfileSorts::SortsAndKinds, interner)?
    else {
        return Ok(());
    };
    // Identities and host term hooks are ground term bubbles. Op hooks carry declaration signatures:
    // reconstruct their referenced operator head while preserving the signature for later sort
    // substitution.
    for op in &mut d.ops {
        if let Some(identity) = &mut op.attrs.id {
            *identity = mapper.rewrite(identity, interner);
        }
        if let Some(special) = &mut op.attrs.special {
            for (_, signature) in &mut special.op_hooks {
                *signature = rewrite_op_hook_signature(signature, op_recon, interner);
            }
            for (_, term) in &mut special.term_hooks {
                *term = mapper.rewrite(term, interner);
            }
        }
    }
    for st in &mut d.statements {
        match st {
            Statement::Eq { lhs, rhs, cond, .. } | Statement::Rule { lhs, rhs, cond, .. } => {
                *lhs = mapper.rewrite(lhs, interner);
                *rhs = mapper.rewrite(rhs, interner);
                if let Some(c) = cond {
                    *c = mapper.rewrite_condition(c, interner);
                }
            }
            Statement::Mb { lhs, cond, .. } => {
                *lhs = mapper.rewrite(lhs, interner);
                if let Some(c) = cond {
                    *c = mapper.rewrite_condition(c, interner);
                }
            }
        }
    }
    for def in &mut d.strat_defs {
        for param in &mut def.params {
            *param = mapper.rewrite(param, interner);
        }
        rewrite_strategy_bubbles_with(&mut def.body, &mut |bubble, is_condition| {
            if is_condition {
                mapper.rewrite_condition(bubble, interner)
            } else {
                mapper.rewrite(bubble, interner)
            }
        });
        if let Some(cond) = &mut def.cond {
            *cond = mapper.rewrite_condition(cond, interner);
        }
    }
    Ok(())
}

/// One parameter's binding for instantiation. `view_name` is the printed argument name used to name
/// structured sorts (`Base{X} ↦ Base{<view_name>}`): the view name `V` for a view argument, or the
/// enclosing parameter name `p` for a by-parameter argument. A view binding maps each theory sort through
/// `sort_image` (`Elt ↦ Nat`); a [`by_param`](Self::by_param) binding instead prefix-renames `X$s ↦
/// view_name$s` (the parameter survives under its enclosing name).
struct ParamBinding {
    view_name: String,
    /// The **final** argument name — the same as `view_name` for a single-level argument, but for a chain
    /// `M{ToT2}{C2}` it is only the *last* level (`C2`), not the joined chain. Used for the by-parameter
    /// `$`-sort rename (`X$s ↦ final_name$s`): a chain ending in an enclosing parameter (`LIST{ORD}{X}`)
    /// must rename `X$Elt ↦ X$Elt`, not `X$Elt ↦ ORD}{X$Elt` — the structured sort keeps the full chain
    /// (`Lst{X} ↦ Lst{ORD}{X}`), but the surviving parameter's sort uses only the last level.
    final_name: String,
    sort_image: HashMap<String, String>,
    by_param: bool,
    /// The parameter theory's own sorts — the sorts `s` for which `X$s` is a *genuine* parameter sort
    /// (theory-declared, excluding module-origin sorts, exactly what [`add_parameter_copy`] renames).
    /// Gates the `X$s` substitution in [`inst_sort`]: a "fake" parameter sort `X$Foo` (`Foo` not a theory
    /// sort — declared directly in the parameterized module's body) must survive instantiation unchanged.
    /// `None` disables the gate for nested-view bindings because their view-map target sorts cannot be
    /// fake parameter sorts.
    theory_sorts: Option<HashSet<String>>,
}

/// One instantiation argument resolved to its parameter binding plus the module expression to import for
/// it. A view argument carries `target = Some(<to-module expression>)`; a **by-parameter**
/// argument (an enclosing parameter passed straight through) carries `target = None` — nothing is imported
/// (the enclosing module's parameter copy already supplied `p$s`).
struct ArgResolution {
    binding: ParamBinding,
    target: Option<ModuleExpr>,
    op_subst: HashMap<String, Vec<Token>>,
    /// Op maps that need grammar-aware reconstruction of the parameterized module's statement bubbles
    /// ([`ViewOpSubst`]): signature-specific maps, mixfix fixity changes, and op→term maps with variable
    /// arguments; see [`op_maps_of`].
    op_recon: Vec<ViewOpMap>,
}

/// Resolve one instantiation argument against the enclosing parameter `scope`. A bare name in `scope` is a
/// by-parameter argument (kind 2). Otherwise a bare view name resolves to the stored view (kind 3 base
/// case), and a nested instantiation `V{Arg, …}` of a *parameterized* view resolves recursively — each
/// inner argument is resolved, then substituted through `V`'s `to` target and `sort_maps` (`BoxV{ToColor}`
/// ⇒ target `BOX{ToColor}`, image `Elt ↦ Box{ToColor}`).
fn resolve_arg(
    arg: &ModuleExpr,
    views: &ViewDb,
    db: &ModuleDb,
    i: &Interner,
    scope: &[String],
) -> Result<ArgResolution, String> {
    // By-parameter: the argument is an enclosing parameter `p`. The instance keeps a parameter, renamed to
    // `p` (`X$s ↦ p$s`, `Base{X} ↦ Base{p}`); nothing is imported.
    if let ModuleExpr::Named(p) = arg
        && scope.iter().any(|n| n == p)
    {
        return Ok(ArgResolution {
            binding: ParamBinding {
                view_name: p.clone(),
                final_name: p.clone(),
                sort_image: HashMap::new(),
                by_param: true,
                theory_sorts: None,
            },
            target: None,
            op_subst: HashMap::new(),
            op_recon: Vec::new(),
        });
    }
    match arg {
        ModuleExpr::Named(view_name) => {
            let v = views
                .get(view_name)
                .ok_or_else(|| format!("view `{view_name}` is not defined"))?;
            if !v.params.is_empty() {
                return Err(format!(
                    "parameterized view `{view_name}` must be instantiated with arguments"
                ));
            }
            let (op_subst, op_recon) = op_maps_of(v, i)?;
            Ok(ArgResolution {
                binding: ParamBinding {
                    view_name: view_name.clone(),
                    final_name: view_name.clone(),
                    sort_image: v.sort_maps.iter().cloned().collect(),
                    by_param: false,
                    theory_sorts: None,
                },
                target: Some(v.to.clone()),
                op_subst,
                op_recon,
            })
        }
        ModuleExpr::Instantiation(base, inner_args) => {
            let ModuleExpr::Named(view_name) = &**base else {
                return Err(
                    "an instantiation argument must be a view name or a parameterized-view \
                            instantiation"
                        .into(),
                );
            };
            let v = views
                .get(view_name)
                .ok_or_else(|| format!("view `{view_name}` is not defined"))?;
            if v.params.len() != inner_args.len() {
                return Err(format!(
                    "view `{view_name}{{…}}` has {} argument(s) but `{view_name}` has {} parameter(s)",
                    inner_args.len(),
                    v.params.len()
                ));
            }
            // Resolve each inner argument and bind `V`'s parameter to it, then substitute through `V`'s
            // target/sort-image to derive the view. The inner views' op maps are applied when their own
            // target is instantiated (via `collect_expr(target)`), not threaded here.
            let mut inner: HashMap<String, ParamBinding> = HashMap::new();
            let mut inner_to_arg: HashMap<String, ModuleExpr> = HashMap::new();
            for (vp, ia) in v.params.iter().zip(inner_args) {
                let r = resolve_arg(ia, views, db, i, scope)?;
                inner_to_arg.insert(vp.name.clone(), ia.clone());
                inner.insert(vp.name.clone(), r.binding);
            }
            let target = subst_params_in_expr(&v.to, &inner_to_arg, db);
            let sort_image = v
                .sort_maps
                .iter()
                .map(|(a, b)| (a.clone(), inst_sort(b, &inner)))
                .collect();
            let (op_subst, op_recon) = op_maps_of(v, i)?;
            Ok(ArgResolution {
                binding: ParamBinding {
                    view_name: canonical_key(arg),
                    final_name: canonical_key(arg),
                    sort_image,
                    by_param: false,
                    theory_sorts: None,
                },
                target: Some(target),
                op_subst,
                op_recon,
            })
        }
        ModuleExpr::Sum(..) | ModuleExpr::Rename(..) => Err(
            "an instantiation argument must be a view name or a parameterized-view instantiation \
                 (a sum/renaming argument is not supported)"
                .into(),
        ),
    }
}

/// The op-maps of a view, split into two application paths:
/// - **textual** (`HashMap` source-token → target token(s)): a non-disambiguated single-token
///   prefix/constant source mapped to a hole-free target, or a constant `op f to term t`. These maps can
///   safely substitute every occurrence of the source name.
/// - **reconstruction** ([`ViewOpMap`]): every signature-disambiguated map, every op→op map where either
///   side is mixfix, and every op→term map with variable arguments. [`ViewOpSubst`] parses each source
///   bubble, resolves the selected source symbol, and re-emits the target syntax.
#[allow(clippy::type_complexity)]
fn op_maps_of(
    v: &ViewDecl,
    i: &Interner,
) -> Result<(HashMap<String, Vec<Token>>, Vec<ViewOpMap>), String> {
    let mut op_subst = HashMap::new();
    let mut op_recon = Vec::new();
    for m in &v.op_maps {
        match m {
            OpMap::Op {
                from,
                to,
                dom_range,
            } => {
                let from_canon: String = from.iter().map(|t| i.resolve(t.sym)).collect();
                let to_canon: String = to.iter().map(|t| i.resolve(t.sym)).collect();
                // A `_` in an op's canonical name is an argument hole (a literal underscore is backtick-
                // escaped), so `contains('_')` distinguishes a mixfix name from a prefix/constant one.
                if dom_range.is_none()
                    && from.len() == 1
                    && !from_canon.contains('_')
                    && !to_canon.contains('_')
                {
                    op_subst.insert(from_canon, to.clone());
                } else {
                    op_recon.push(ViewOpMap {
                        source: from_canon,
                        dom_range: dom_range.clone(),
                        target: ReconTarget::Op(to_canon),
                    });
                }
            }
            OpMap::Term {
                from,
                to,
                dom_range,
            } => match from.as_slice() {
                // A non-disambiguated constant op→term (`op 0 to term 0.0`): a plain token substitution.
                [tok] if dom_range.is_none() => {
                    op_subst.insert(i.resolve(tok.sym).to_string(), to.clone());
                }
                // `op f(A, B, …) to term <template>`: a prefix source applied to argument variables.
                _ => {
                    let (name, formals) = op_pattern_formals(from, i)
                        .or_else(|| mixfix_pattern_formals(from, &v.vars, i))
                        .or_else(|| {
                            dom_range.as_ref().map(|_| {
                                (from.iter().map(|t| i.resolve(t.sym)).collect(), Vec::new())
                            })
                        })
                        .ok_or_else(|| {
                            format!(
                                "view `{}`: malformed operator-to-term source pattern",
                                v.name
                            )
                        })?;
                    op_recon.push(ViewOpMap {
                        source: name,
                        dom_range: dom_range.clone(),
                        target: ReconTarget::Term {
                            formals,
                            template: to.clone(),
                        },
                    });
                }
            },
        }
    }
    Ok((op_subst, op_recon))
}

/// Parse an op-to-term source pattern `name(a1, a2, …)` whose arguments are single-token variables.
/// Returns `None` for mixfix sources or non-variable arguments, which this mapping form does not support.
fn op_pattern_formals(from: &[Token], i: &Interner) -> Option<(String, Vec<String>)> {
    if from.len() < 3 || i.resolve(from[1].sym) != "(" || i.resolve(from[from.len() - 1].sym) != ")"
    {
        return None;
    }
    let name = i.resolve(from[0].sym).to_string();
    let inner = &from[2..from.len() - 1];
    let mut formals = Vec::new();
    let mut depth = 0i32;
    let mut seg: Vec<&Token> = Vec::new();
    for t in inner {
        match i.resolve(t.sym) {
            "(" | "{" | "[" => {
                depth += 1;
                seg.push(t);
            }
            ")" | "}" | "]" => {
                depth -= 1;
                seg.push(t);
            }
            "," if depth == 0 => {
                formals.push(seg_base_name(&seg, i)?);
                seg.clear();
            }
            _ => seg.push(t),
        }
    }
    formals.push(seg_base_name(&seg, i)?);
    Some((name, formals))
}

/// The base variable name of a single-token argument segment `A:Elt` → `"A"`. `None` if the segment is not
/// exactly one token.
fn seg_base_name(seg: &[&Token], i: &Interner) -> Option<String> {
    match seg {
        [t] => {
            let text = i.resolve(t.sym);
            Some(text.split(':').next().unwrap_or(text).to_string())
        }
        _ => None,
    }
}

/// Derive a mixfix operator's canonical name and formal order from a view's source pattern. Source views
/// identify variables through their declarations; reflected views have no declaration list, but their
/// meta-term variables round-trip as explicit `name:Sort` tokens. Thus `to O from O' answer(X)` and its
/// qualified form both become `("to_from_answer(_)", ["O", "O'", "X"])`.
fn mixfix_pattern_formals(
    from: &[Token],
    vars: &[VarDecl],
    i: &Interner,
) -> Option<(String, Vec<String>)> {
    let declared: HashSet<&str> = vars
        .iter()
        .flat_map(|declaration| declaration.names.iter().map(String::as_str))
        .collect();
    let mut name = String::new();
    let mut formals = Vec::new();
    for token in from {
        let text = i.resolve(token.sym);
        let base = text.split(':').next().unwrap_or(text);
        let qualified = text
            .rsplit_once(':')
            .is_some_and(|(name, sort)| !name.is_empty() && !sort.is_empty());
        if declared.contains(base) || qualified {
            name.push('_');
            formals.push(base.to_string());
        } else {
            name.push_str(text);
        }
    }
    (!formals.is_empty() && name.contains('_')).then_some((name, formals))
}

/// Substitute view parameters into a module expression (a parameterized view's `to` target): replace each
/// `Named(p)` that is a parameter with its argument expression, recursing through sums/renamings/nested
/// instantiations. `BoxV`'s target `BOX{X}` with `X ↦ ToColor` becomes `BOX{ToColor}`.
/// Whether the expression's spine contains an instantiation (its root module's parameters are
/// bound somewhere below).
fn spine_has_instantiation(e: &ModuleExpr) -> bool {
    match e {
        ModuleExpr::Instantiation(..) => true,
        ModuleExpr::Rename(inner, _) => spine_has_instantiation(inner),
        ModuleExpr::Named(_) | ModuleExpr::Sum(..) => false,
    }
}

/// The root named module of an expression, through renamings and instantiation chains.
fn expr_root_name(e: &ModuleExpr) -> Option<&str> {
    match e {
        ModuleExpr::Named(n) => Some(n),
        ModuleExpr::Rename(inner, _) => expr_root_name(inner),
        ModuleExpr::Instantiation(base, _) => expr_root_name(base),
        ModuleExpr::Sum(..) => None,
    }
}

fn subst_params_in_expr(
    expr: &ModuleExpr,
    map: &HashMap<String, ModuleExpr>,
    db: &ModuleDb,
) -> ModuleExpr {
    match expr {
        ModuleExpr::Named(n) => map.get(n).cloned().unwrap_or_else(|| expr.clone()),
        ModuleExpr::Sum(a, b) => ModuleExpr::Sum(
            Box::new(subst_params_in_expr(a, map, db)),
            Box::new(subst_params_in_expr(b, map, db)),
        ),
        ModuleExpr::Rename(inner, items) => {
            use tnk_frontend::surface::ast::RenameItem;
            // Substitute enclosing parameters in renaming item names so chained spellings match instance
            // sorts (`List{STO}{X}` becomes `List{STO}{Nat<}`). A rename directly over an uninstantiated
            // parameterized module instead names that module's own parameters; those names are shielded
            // from same-named enclosing parameters because renaming precedes positional instantiation.
            // Once the inner spine is instantiated, its brace arguments belong to the enclosing scope and
            // are substituted.
            let inner_params: HashSet<&str> = if spine_has_instantiation(inner) {
                HashSet::new()
            } else {
                expr_root_name(inner)
                    .and_then(|n| db.get(n))
                    .map(|pm| pm.params.iter().map(|p| p.name.as_str()).collect())
                    .unwrap_or_default()
            };
            let names: HashMap<String, String> = map
                .iter()
                .filter(|(p, _)| !inner_params.contains(p.as_str()))
                .map(|(p, a)| (p.clone(), canonical_key(a)))
                .collect();
            let new_items: Vec<RenameItem> = items
                .iter()
                .map(|it| match it {
                    RenameItem::Sort { from, to } => RenameItem::Sort {
                        from: subst_param_name(from, &names),
                        to: subst_param_name(to, &names),
                    },
                    RenameItem::Op {
                        from,
                        to,
                        dom_range,
                        attrs,
                    } => RenameItem::Op {
                        from: subst_param_name(from, &names),
                        to: subst_param_name(to, &names),
                        dom_range: dom_range.as_ref().map(|(d, r)| {
                            (
                                d.iter().map(|s| subst_param_name(s, &names)).collect(),
                                subst_param_name(r, &names),
                            )
                        }),
                        attrs: attrs.clone(),
                    },
                    RenameItem::Label { from, to } => RenameItem::Label {
                        from: from.clone(),
                        to: to.clone(),
                    },
                })
                .collect();
            ModuleExpr::Rename(Box::new(subst_params_in_expr(inner, map, db)), new_items)
        }
        ModuleExpr::Instantiation(base, args) => ModuleExpr::Instantiation(
            Box::new(subst_params_in_expr(base, map, db)),
            args.iter()
                .map(|a| subst_params_in_expr(a, map, db))
                .collect(),
        ),
    }
}

/// Substitute parameter names in a (possibly structured / chained) sort or op name: each identifier token
/// — a maximal run between `{`, `}`, `,` — that is a parameter is replaced by its argument name. Brace/
/// comma delimiting means a *chain* `List{STO}{X}` and a nested `Pair{X, Y}` both substitute correctly
/// (`X ↦ Nat<` gives `List{STO}{Nat<}`); an unrelated token like `STRICT-TOTAL-ORDER` is left as-is.
fn subst_param_name(name: &str, names: &HashMap<String, String>) -> String {
    let mut out = String::new();
    let mut ident = String::new();
    for c in name.chars() {
        if matches!(c, '{' | '}' | ',') {
            if !ident.is_empty() {
                out.push_str(
                    names
                        .get(ident.as_str())
                        .map(String::as_str)
                        .unwrap_or(&ident),
                );
                ident.clear();
            }
            out.push(c);
        } else {
            ident.push(c);
        }
    }
    if !ident.is_empty() {
        out.push_str(
            names
                .get(ident.as_str())
                .map(String::as_str)
                .unwrap_or(&ident),
        );
    }
    out
}

/// Apply the instantiation substitution to a module's own declarations: rewrite every sort name through
/// [`inst_sort`], and rewrite the view's operator maps into the statement bubbles — each reference to
/// a mapped theory operator `f` becomes the target operator `g` or term `t`.
fn instantiate_decls(
    mut d: FlatDecls,
    bindings: &HashMap<String, ParamBinding>,
    op_subst: &HashMap<String, Vec<Token>>,
    i: &mut Interner,
) -> FlatDecls {
    for s in &mut d.sorts {
        *s = inst_sort(s, bindings);
    }
    for chain in &mut d.subsorts {
        for group in chain {
            for s in group {
                *s = inst_sort(s, bindings);
            }
        }
    }
    for op in &mut d.ops {
        let name: String = op.name.iter().map(|token| i.resolve(token.sym)).collect();
        let instantiated_name = inst_sort(&name, bindings);
        if instantiated_name != name {
            op.name = tokenize(&instantiated_name, i);
        }
        for s in &mut op.domain {
            *s = inst_sort(s, bindings);
        }
        op.range = inst_sort(&op.range, bindings);
    }
    // Instantiate each declared variable's sort, and record `name ↦ instantiated sort` so the variable's
    // occurrences in the statement bubbles can be rewritten to single-token colon variables below. (The
    // declarations are kept for bare-variable use in commands, but the bubbles no longer reference them.)
    let mut var_inline: HashMap<String, String> = HashMap::new();
    for v in &mut d.vars {
        v.sort = inst_sort(&v.sort, bindings);
        for n in &v.names {
            var_inline.insert(n.clone(), v.sort.clone());
        }
    }
    // An identity is a signature-owned ground term. It follows the same view/operator and parameter-sort
    // substitution as statement terms, but never receives variable inlining (groundness is checked by the
    // frontend when the rebuilt signature installs it).
    let no_vars = HashMap::new();
    for op in &mut d.ops {
        if let Some(identity) = &mut op.attrs.id {
            *identity = subst_bubble(identity, bindings, op_subst, &no_vars, i);
        }
        if let Some(special) = &mut op.attrs.special {
            for (_, signature) in &mut special.op_hooks {
                *signature = subst_bubble(signature, bindings, op_subst, &no_vars, i);
            }
            for (_, term) in &mut special.term_hooks {
                *term = subst_bubble(term, bindings, op_subst, &no_vars, i);
            }
        }
    }
    // Rewrite statement bubbles: each view operator map; each declared variable inlined as a
    // single-token colon variable at its instantiated sort (`H ↦ H:List{ToN}`); and parameter-sort
    // substitution inside glued source colon variables (`E:X$Elt ↦ E:Box{ToColor}`). The colon-variable
    // form keeps the sort a single token that re-parses against the instance's sorts — essential because a
    // nested instantiation produces two copies of a parameterized module's equations at *different* element
    // sorts, which a shared module-level `var` declaration (deduplicated by name) could not type.
    for st in &mut d.statements {
        match st {
            Statement::Eq { lhs, rhs, cond, .. } => {
                *lhs = subst_bubble(lhs, bindings, op_subst, &var_inline, i);
                *rhs = subst_bubble(rhs, bindings, op_subst, &var_inline, i);
                if let Some(c) = cond {
                    *c = subst_bubble(c, bindings, op_subst, &var_inline, i);
                }
            }
            Statement::Mb {
                lhs, sort, cond, ..
            } => {
                *lhs = subst_bubble(lhs, bindings, op_subst, &var_inline, i);
                // The membership's *sort* is a whole sort name (possibly structured, `NeList{X}`):
                // instantiate it as a sort, not as a term bubble.
                *sort = inst_sort_bubble(sort, bindings, i);
                if let Some(c) = cond {
                    *c = subst_bubble(c, bindings, op_subst, &var_inline, i);
                }
            }
            Statement::Rule { lhs, rhs, cond, .. } => {
                *lhs = subst_bubble(lhs, bindings, op_subst, &var_inline, i);
                *rhs = subst_bubble(rhs, bindings, op_subst, &var_inline, i);
                if let Some(c) = cond {
                    *c = subst_bubble(c, bindings, op_subst, &var_inline, i);
                }
            }
        }
    }
    let mut instance_parts: Vec<_> = bindings
        .iter()
        .map(|(parameter, binding)| format!("{parameter}={}", binding.view_name))
        .collect();
    instance_parts.sort();
    let instance_key = instance_parts.join(",");
    for decl in &mut d.strat_decls {
        for sort in &mut decl.domain {
            *sort = inst_sort(sort, bindings);
        }
        decl.subject = inst_sort(&decl.subject, bindings);
        decl.home = None;
        if let Some(origin) = &mut decl.origin {
            origin.push('{');
            origin.push_str(&instance_key);
            origin.push('}');
        }
    }
    for def in &mut d.strat_defs {
        def.home = None;
        if let Some(origin) = &mut def.origin {
            origin.push('{');
            origin.push_str(&instance_key);
            origin.push('}');
        }
        for param in &mut def.params {
            *param = subst_bubble(param, bindings, op_subst, &var_inline, i);
        }
        rewrite_strategy_bubbles(&mut def.body, &mut |bubble| {
            subst_bubble(bubble, bindings, op_subst, &var_inline, i)
        });
        if let Some(cond) = &mut def.cond {
            *cond = subst_bubble(cond, bindings, op_subst, &var_inline, i);
        }
    }
    d
}

/// Instantiate a membership's sort bubble: reassemble the (possibly structured) sort name, run it through
/// [`inst_sort`] (`NeList{X} ↦ NeList{ToN}`, `X$Elt ↦ Nat`), and re-tokenize. Unchanged sorts keep their
/// original tokens.
fn inst_sort_bubble(
    sort: &[Token],
    bindings: &HashMap<String, ParamBinding>,
    i: &mut Interner,
) -> Vec<Token> {
    let name: String = sort.iter().map(|t| i.resolve(t.sym)).collect();
    let new = inst_sort(&name, bindings);
    if new == name {
        sort.to_vec()
    } else {
        tokenize(&new, i)
    }
}

/// Rewrite a statement bubble under an instantiation. A token that is a mapped source operator becomes its
/// target token(s) (op→op / op→term). A bare declared-variable token becomes a single-token colon
/// variable at its instantiated sort (`H ↦ H:List{ToN}`, from `var_inline`). A glued source colon variable
/// `name:sort` has its sort instantiated (`E:X$Elt ↦ E:Box{ToColor}`). Each rewritten variable stays one
/// token, so it re-parses as an on-the-fly variable of the instance sort; a `name:sort` whose sort is
/// unaffected by the instantiation is left untouched (so an operator coincidentally containing a colon is
/// safe).
fn subst_bubble(
    bubble: &[Token],
    bindings: &HashMap<String, ParamBinding>,
    op_subst: &HashMap<String, Vec<Token>>,
    var_inline: &HashMap<String, String>,
    i: &mut Interner,
) -> Vec<Token> {
    let mut out = Vec::with_capacity(bubble.len());
    let mut idx = 0;
    while idx < bubble.len() {
        let t = bubble[idx];
        let text = i.resolve(t.sym).to_string();
        let attached_sort = text
            .strip_prefix('.')
            .filter(|sort| !sort.is_empty())
            .map(str::to_string);
        let separate_sort =
            (idx > 0 && i.resolve(bubble[idx - 1].sym) == ".").then(|| text.clone());
        if let Some(mut sort) = attached_sort.as_ref().or(separate_sort.as_ref()).cloned() {
            let mut end = idx + 1;
            if sort == "[" {
                let mut depth = 1usize;
                while end < bubble.len() && depth != 0 {
                    let fragment = i.resolve(bubble[end].sym);
                    sort.push_str(fragment);
                    depth += usize::from(fragment == "[");
                    depth = depth.saturating_sub(usize::from(fragment == "]"));
                    end += 1;
                }
            } else {
                while end < bubble.len() && i.resolve(bubble[end].sym) == "{" {
                    let mut depth = 0usize;
                    while end < bubble.len() {
                        let fragment = i.resolve(bubble[end].sym);
                        sort.push_str(fragment);
                        depth += usize::from(fragment == "{");
                        depth = depth.saturating_sub(usize::from(fragment == "}"));
                        end += 1;
                        if depth == 0 {
                            break;
                        }
                    }
                }
            }
            let mapped_sort = inst_sort(&sort, bindings);
            if mapped_sort != sort {
                let mapped = if attached_sort.is_some() {
                    format!(".{mapped_sort}")
                } else {
                    mapped_sort
                };
                out.extend(tokenize(&mapped, i));
                idx = end;
                continue;
            }
        }
        // Structured operator/class names are tokenized as `Base { Args } ...`; instantiate every chained
        // brace group just like the corresponding sort declaration (`SortedList{X}` → `SortedList{NatW}`).
        if idx + 1 < bubble.len() && i.resolve(bubble[idx + 1].sym) == "{" {
            let mut name = text.clone();
            let mut end = idx + 1;
            while end < bubble.len() && i.resolve(bubble[end].sym) == "{" {
                let mut depth = 0usize;
                while end < bubble.len() {
                    let fragment = i.resolve(bubble[end].sym);
                    name.push_str(fragment);
                    depth += usize::from(fragment == "{");
                    depth = depth.saturating_sub(usize::from(fragment == "}"));
                    end += 1;
                    if depth == 0 {
                        break;
                    }
                }
            }
            let mapped = inst_sort(&name, bindings);
            if mapped != name {
                out.extend(tokenize(&mapped, i));
                idx = end;
                continue;
            }
        }
        if let Some(repl) = op_subst.get(&text) {
            out.extend(repl.iter().copied());
            idx += 1;
            continue;
        }
        if let Some((base, count)) = text.rsplit_once('^')
            && !base.is_empty()
            && !count.is_empty()
            && count.bytes().all(|b| b.is_ascii_digit())
            && let Some(repl) = op_subst.get(base)
            && let [target] = repl.as_slice()
        {
            // Compact iter syntax glues the scalar count to the source operator (`g^N`). A view maps
            // operator identity, so re-root the token at its one-token target while retaining `N`.
            let mapped = format!("{}^{count}", i.resolve(target.sym));
            let mut nt = t;
            nt.sym = i.intern(&mapped);
            out.push(nt);
            idx += 1;
            continue;
        }
        if let Some(sort) = var_inline.get(&text) {
            let mut nt = t;
            nt.sym = i.intern(&format!("{text}:{sort}"));
            out.push(nt);
            idx += 1;
            continue;
        }
        if let Some((name, sort)) = text.rsplit_once(':')
            && !name.is_empty()
            && !sort.is_empty()
        {
            let new_sort = inst_sort(sort, bindings);
            if new_sort.as_str() != sort {
                let mut nt = t;
                nt.sym = i.intern(&format!("{name}:{new_sort}"));
                out.push(nt);
                idx += 1;
                continue;
            }
        }
        let mapped_sort = inst_sort(&text, bindings);
        if mapped_sort != text {
            let mut nt = t;
            nt.sym = i.intern(&mapped_sort);
            out.push(nt);
            idx += 1;
            continue;
        }
        out.push(t);
        idx += 1;
    }
    out
}

/// Instantiate one sort name. A parameter sort `X$s` becomes the view's image of `s` (or `p$s` under a
/// by-parameter binding); a structured sort `Base{a, …}` has each argument instantiated (a bare parameter
/// name `X` becomes its view/argument name, the instance-naming rule); anything else is unchanged.
fn inst_sort(name: &str, bindings: &HashMap<String, ParamBinding>) -> String {
    // A kind spelling instantiates each of its component sorts (`[Y$Elt] ↦ [Nat]`, MAP's
    // `op undefined : -> [Y$Elt]`; `[S{X},T{X}] ↦ [S{V},T{V}]`). Its bracket text is not one sort name.
    if let Some(components) = kind_components(name) {
        let instantiated: Vec<String> = components
            .iter()
            .map(|component| inst_sort(component, bindings))
            .collect();
        return format!("[{}]", instantiated.join(","));
    }
    if let Some((base, groups)) = split_structured(name) {
        let mut instantiated = base.to_string();
        for args in groups {
            let new_args: Vec<String> = args
                .iter()
                .map(|a| match bindings.get(a.as_str()) {
                    Some(b) => b.view_name.clone(), // a bare parameter name → the view / argument name
                    None => inst_sort(a, bindings), // nested structured / parameter sort
                })
                .collect();
            instantiated.push('{');
            instantiated.push_str(&new_args.join(","));
            instantiated.push('}');
        }
        return instantiated;
    }
    if let Some((param, s)) = name.split_once('$')
        && let Some(b) = bindings.get(param)
    {
        // A name `X$Foo` where `Foo` is not a sort of X's theory is an ordinary sort name and survives
        // instantiation. Nested-view internal bindings omit this ownership gate.
        if let Some(ts) = &b.theory_sorts
            && !ts.contains(s)
        {
            return name.to_string();
        }
        // By-parameter: prefix-rename `X$s ↦ p$s` (the parameter survives) — using the *final* level only,
        // so a chain `LIST{ORD}{X}` gives `X$Elt`, not the malformed chain `ORD}{X$Elt`. View: the view's
        // sort image.
        return if b.by_param {
            format!("{}${s}", b.final_name)
        } else {
            b.sort_image
                .get(s)
                .cloned()
                .unwrap_or_else(|| s.to_string())
        };
    }
    name.to_string()
}

/// Split a structured sort name into its base and chained top-level argument groups:
/// `Base{A,B}{X}` becomes `("Base", [["A", "B"], ["X"]])`. Nested structured arguments stay intact.
fn split_structured(name: &str) -> Option<(&str, Vec<Vec<String>>)> {
    let open = name.find('{')?;
    let base = &name[..open];
    let mut groups = Vec::new();
    let mut current = Vec::new();
    let mut depth = 0usize;
    let mut start = open + 1;
    let mut end = open;

    for (idx, c) in name.char_indices().skip_while(|(idx, _)| *idx < open) {
        match c {
            '{' => {
                if depth == 0 {
                    if idx != open && idx != end {
                        return None;
                    }
                    current.clear();
                    start = idx + 1;
                }
                depth += 1;
            }
            ',' if depth == 1 => {
                current.push(name[start..idx].to_string());
                start = idx + 1;
            }
            '}' => {
                depth = depth.checked_sub(1)?;
                if depth == 0 {
                    current.push(name[start..idx].to_string());
                    groups.push(std::mem::take(&mut current));
                    end = idx + 1;
                }
            }
            _ if depth == 0 => return None,
            _ => {}
        }
    }
    (depth == 0 && end == name.len() && groups.iter().all(|group| !group.is_empty()))
        .then_some((base, groups))
}

/// A canonical string for a module expression, used as the `visited` dedup key.
fn canonical_key(expr: &ModuleExpr) -> String {
    match expr {
        ModuleExpr::Named(n) => n.clone(),
        ModuleExpr::Sum(a, b) => format!("({} + {})", canonical_key(a), canonical_key(b)),
        ModuleExpr::Rename(inner, items) => {
            use tnk_frontend::surface::ast::RenameItem;
            let parts: Vec<String> = items
                .iter()
                .map(|it| match it {
                    RenameItem::Sort { from, to } => format!("sort {from} to {to}"),
                    RenameItem::Op {
                        from,
                        to,
                        dom_range: Some((d, r)),
                        ..
                    } => {
                        format!("op {from} : {} -> {r} to {to}", d.join(" "))
                    }
                    RenameItem::Op { from, to, .. } => format!("op {from} to {to}"),
                    RenameItem::Label { from, to } => format!("label {from} to {to}"),
                })
                .collect();
            format!("({} * ({}))", canonical_key(inner), parts.join(", "))
        }
        ModuleExpr::Instantiation(base, args) => {
            // Canonical instance name `M{A, …}`; each argument is itself a module expression.
            let parts: Vec<String> = args.iter().map(canonical_key).collect();
            format!("{}{{{}}}", canonical_key(base), parts.join(","))
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tnk_frontend::lex::tokenize;
    use tnk_frontend::surface::parser::Parser;

    fn db_of(src: &str) -> (ModuleDb, ViewDb, Interner) {
        let mut i = Interner::new();
        let toks = tokenize(src, &mut i);
        let s = Parser::new(&toks, &i).parse_source().expect("parse");
        let db = ModuleDb::from_modules(s.modules);
        let mut views = ViewDb::new();
        for v in s.views {
            crate::view::validate_view(&v, &db, &views, &mut i).expect("valid view");
            views.insert(v);
        }
        (db, views, i)
    }

    /// A diamond (`TOP` imports `L` and `R`, both protecting `BASE`) includes `BASE`'s declarations
    /// exactly once.
    #[test]
    fn diamond_includes_base_once() {
        let src = "\
fmod BASE is sort S . op a : -> S [ctor] . op f : S -> S . var X : S . eq f(X) = a . endfm
fmod L is protecting BASE . op l : S -> S . endfm
fmod R is protecting BASE . op r : S -> S . endfm
fmod TOP is protecting L . protecting R . endfm
";
        let (db, views, mut i) = db_of(src);
        let flat = flatten("TOP", &db, &views, &mut i).expect("flatten");
        assert_eq!(
            flat.sorts,
            ["S"],
            "BASE's sort S appears once despite two import paths"
        );
        assert_eq!(
            flat.statements.len(),
            1,
            "BASE's single equation is not duplicated"
        );
        let opnames: Vec<String> = flat
            .ops
            .iter()
            .map(|o| i.resolve(o.name[0].sym).to_string())
            .collect();
        assert!(
            ["a", "f", "l", "r"]
                .iter()
                .all(|n| opnames.contains(&n.to_string()))
        );
    }

    /// An import-free module flattens to itself (so `load_program` handles single-module files).
    #[test]
    fn import_free_flattens_to_itself() {
        let (db, views, mut i) = db_of("fmod M is sort S . op a : -> S [ctor] . endfm\n");
        let flat = flatten("M", &db, &views, &mut i).expect("flatten");
        assert!(flat.imports.is_empty());
        assert_eq!(flat.sorts, ["S"]);
    }

    /// A parameter `X :: TRIV` makes a parameter copy of `TRIV` — the theory sort `Elt` becomes the
    /// parameter sort `X$Elt` in the flattened module, alongside the module's own structured sort, and no
    /// formal parameters remain.
    #[test]
    fn parameter_copy_introduces_param_sort() {
        let (db, views, mut i) = db_of(
            "fth TRIV is sort Elt . endfth\n\
             fmod BOX{X :: TRIV} is sort Box{X} . op b : X$Elt -> Box{X} [ctor] . endfm\n",
        );
        let flat = flatten("BOX", &db, &views, &mut i).expect("flatten");
        assert!(
            flat.sorts.contains(&"X$Elt".to_string()),
            "X$Elt present: {:?}",
            flat.sorts
        );
        assert!(
            flat.sorts.contains(&"Box{X}".to_string()),
            "Box{{X}} present: {:?}",
            flat.sorts
        );
        assert!(
            flat.params.is_empty(),
            "no formal parameters remain after flattening"
        );
    }

    /// Instantiation `BOX{V}` resolves to the parameter sort's view image and the structured sort's
    /// instance name — `X$Elt ↦ Hue` (the view's `sort Elt to Hue`) and `Box{X} ↦ Box{V}`. The view's
    /// target module's sorts (`Hue`) are imported.
    #[test]
    fn instantiation_substitutes_param_and_structured_sorts() {
        let (db, views, mut i) = db_of(
            "fth TRIV is sort Elt . endfth\n\
             fmod COLOR is sort Hue . op red : -> Hue [ctor] . endfm\n\
             view V from TRIV to COLOR is sort Elt to Hue . endv\n\
             fmod BOX{X :: TRIV} is sort Box{X} . op wrap : X$Elt -> Box{X} [ctor] . endfm\n\
             fmod USE is protecting BOX{V} . endfm\n",
        );
        let flat = flatten("USE", &db, &views, &mut i).expect("flatten");
        assert!(
            flat.sorts.contains(&"Box{V}".to_string()),
            "structured instance sort: {:?}",
            flat.sorts
        );
        assert!(
            flat.sorts.contains(&"Hue".to_string()),
            "view target sort imported: {:?}",
            flat.sorts
        );
        assert!(
            !flat.sorts.contains(&"X$Elt".to_string()),
            "parameter sort is substituted away"
        );
        assert!(
            !flat.sorts.contains(&"Box{X}".to_string()),
            "parameterized sort is instantiated"
        );
        // `wrap` now has domain `Hue` (the view image of `X$Elt`).
        let wrap = flat
            .ops
            .iter()
            .find(|o| i.resolve(o.name[0].sym) == "wrap")
            .expect("wrap op");
        assert_eq!(
            wrap.domain,
            ["Hue"],
            "X$Elt domain substituted to the view image"
        );
        assert_eq!(wrap.range, "Box{V}");
    }

    /// A nested instantiation `BOX{BoxV{ToColor}}` resolves the parameterized-view argument
    /// `BoxV{ToColor}` to a derived ground view (target `BOX{ToColor}`, sort image `Elt ↦ Box{ToColor}`),
    /// so the flattened module carries both element-level instances of `Box` and both `wrap` overloads —
    /// `wrap : Hue -> Box{ToColor}` (the inner target) and `wrap : Box{ToColor} -> Box{BoxV{ToColor}}`.
    #[test]
    fn nested_instantiation_resolves_derived_view() {
        let (db, views, mut i) = db_of(
            "fth TRIV is sort Elt . endfth\n\
             fmod COLOR is sort Hue . op red : -> Hue [ctor] . endfm\n\
             view ToColor from TRIV to COLOR is sort Elt to Hue . endv\n\
             fmod BOX{X :: TRIV} is sort Box{X} . op wrap : X$Elt -> Box{X} [ctor] . endfm\n\
             view BoxV{X :: TRIV} from TRIV to BOX{X} is sort Elt to Box{X} . endv\n\
             fmod USE is protecting BOX{BoxV{ToColor}} . endfm\n",
        );
        let flat = flatten("USE", &db, &views, &mut i).expect("flatten");
        for s in ["Hue", "Box{ToColor}", "Box{BoxV{ToColor}}"] {
            assert!(
                flat.sorts.contains(&s.to_string()),
                "sort {s} present: {:?}",
                flat.sorts
            );
        }
        // Both `wrap` overloads: the inner `Hue -> Box{ToColor}` and the outer `Box{ToColor} -> Box{…}`.
        let wraps: Vec<(&Vec<String>, &String)> = flat
            .ops
            .iter()
            .filter(|o| i.resolve(o.name[0].sym) == "wrap")
            .map(|o| (&o.domain, &o.range))
            .collect();
        assert!(
            wraps
                .iter()
                .any(|(d, r)| d.as_slice() == ["Hue"] && r.as_str() == "Box{ToColor}"),
            "inner wrap: {wraps:?}"
        );
        assert!(
            wraps.iter().any(
                |(d, r)| d.as_slice() == ["Box{ToColor}"] && r.as_str() == "Box{BoxV{ToColor}}"
            ),
            "outer wrap: {wraps:?}"
        );
    }

    /// A parameterized module `PAIR{X :: TRIV}` protects `LIST{X}` by the *enclosing
    /// parameter* `X`. Flattened **standalone** it stays parameterized — the `LIST{X}` import is a
    /// by-parameter instantiation, so `LIST`'s `E$Elt` / `List{E}` are renamed to `X$Elt` / `List{X}`.
    #[test]
    fn by_parameter_import_stays_parameterized() {
        let (db, views, mut i) = db_of(
            "fth TRIV is sort Elt . endfth\n\
             fmod LIST{E :: TRIV} is sort List{E} . op cons : E$Elt List{E} -> List{E} [ctor] . endfm\n\
             fmod PAIR{X :: TRIV} is protecting LIST{X} . op two : X$Elt -> List{X} . endfm\n",
        );
        let flat = flatten("PAIR", &db, &views, &mut i).expect("flatten");
        assert!(
            flat.sorts.contains(&"List{X}".to_string()),
            "List{{X}} present: {:?}",
            flat.sorts
        );
        assert!(
            flat.sorts.contains(&"X$Elt".to_string()),
            "X$Elt present: {:?}",
            flat.sorts
        );
        // `cons` came from `LIST{X}` with its parameter `E` renamed to `X`: `X$Elt List{X} -> List{X}`.
        let cons = flat
            .ops
            .iter()
            .find(|o| i.resolve(o.name[0].sym) == "cons")
            .expect("cons");
        assert_eq!(cons.domain, ["X$Elt", "List{X}"]);
        assert_eq!(cons.range, "List{X}");
    }

    /// Instantiation rewrites every component of a multi-sort kind spelling (TNK-MOD-004): the bracket
    /// text is not one sort name. Structured components, parameter sorts, and either order instantiate.
    #[test]
    fn instantiation_substitutes_every_kind_component() {
        let (db, views, mut i) = db_of(
            "fth TRIV is sort Elt . endfth\n\
             fmod COLOR is sort Hue . op red : -> Hue [ctor] . endfm\n\
             view V from TRIV to COLOR is sort Elt to Hue . endv\n\
             fmod K{X :: TRIV} is\n\
               sorts S{X} T{X} L{X} .\n\
               subsort X$Elt < S{X} T{X} L{X} .\n\
               op fa : [S{X},T{X}] -> [S{X},T{X}] .\n\
               op fb : [X$Elt,S{X}] -> [X$Elt] .\n\
               op fc : [L{X},X$Elt] -> [L{X}] .\n\
               var W : [S{X},T{X}] .\n\
             endfm\n\
             fmod USE is protecting K{V} . endfm\n",
        );
        let flat = flatten("USE", &db, &views, &mut i).expect("flatten");
        let profile = |name: &str| {
            let op = flat
                .ops
                .iter()
                .find(|o| i.resolve(o.name[0].sym) == name)
                .unwrap_or_else(|| panic!("op {name}"));
            (op.domain.clone(), op.range.clone())
        };
        assert_eq!(
            profile("fa"),
            (vec!["[S{V},T{V}]".to_string()], "[S{V},T{V}]".to_string())
        );
        assert_eq!(
            profile("fb"),
            (vec!["[Hue,S{V}]".to_string()], "[Hue]".to_string())
        );
        assert_eq!(
            profile("fc"),
            (vec!["[L{V},Hue]".to_string()], "[L{V}]".to_string())
        );
        let w = flat
            .vars
            .iter()
            .find(|v| v.names.iter().any(|n| n == "W"))
            .expect("var W");
        assert_eq!(w.sort, "[S{V},T{V}]");
    }

    /// The rename items of an instantiated renamed module `(M * R){V}` take the instance's parameter
    /// names inside kind-spelled profile sorts as well as in structured sort names.
    #[test]
    fn renamed_instance_substitutes_kind_profile_parameters() {
        let (db, _, mut i) = db_of(
            "fth TRIV is sort Elt . endfth\n\
             fmod L{X :: TRIV} is sort List{X} . op f : [List{X}] -> [List{X}] . endfm\n",
        );
        let toks = tokenize(
            "fmod U is inc (L * (sort List{X} to Seq{X}, \
             op f : [List{X}] X$Elt -> [List{X},X$Elt] to g)){V} . endfm",
            &mut i,
        );
        let source = Parser::new(&toks, &i).parse_source().expect("parse");
        let ModuleExpr::Instantiation(base, args) = &source.modules[0].imports[0].expr else {
            panic!("instantiated import");
        };
        let ModuleExpr::Rename(inner, items) = &**base else {
            panic!("renamed base");
        };
        let items = subst_rename_item_params(inner, args, &db, items);
        assert!(
            matches!(&items[0], RenameItem::Sort { from, to } if from == "List{V}" && to == "Seq{V}"),
            "structured sort item"
        );
        let RenameItem::Op {
            dom_range: Some((domain, range)),
            ..
        } = &items[1]
        else {
            panic!("profiled op item");
        };
        assert_eq!(domain, &["[List{V}]", "X$Elt"]);
        assert_eq!(range, "[List{V},X$Elt]");
    }

    /// An undefined imported module is a loud error.
    #[test]
    fn unknown_import_errors() {
        let (db, views, mut i) = db_of("fmod M is protecting NOPE . endfm\n");
        let err = flatten("M", &db, &views, &mut i).unwrap_err();
        assert!(err.contains("not defined"), "got: {err}");
    }

    #[test]
    fn strategy_diamonds_dedup_by_origin_not_identical_text() {
        let (db, views, mut interner) = db_of(
            "mod STRAT-COMMON is sort S . op a : -> S . endm
             smod STRAT-BASE is
               protecting STRAT-COMMON .
               strat shared : @ S .
               sd shared := idle .
             endsm
             smod STRAT-LEFT is
               protecting STRAT-BASE .
               strat twin : @ S .
               sd twin := idle .
             endsm
             smod STRAT-RIGHT is
               protecting STRAT-BASE .
               strat twin : @ S .
               sd twin := idle .
             endsm
             smod STRAT-TOP is
               protecting STRAT-LEFT .
               protecting STRAT-RIGHT .
             endsm",
        );
        let flat = flatten("STRAT-TOP", &db, &views, &mut interner).expect("flatten");
        assert_eq!(
            flat.strat_decls
                .iter()
                .filter(|declaration| declaration.name == "shared")
                .count(),
            1,
            "the shared base origin is donated once through the diamond"
        );
        assert_eq!(
            flat.strat_defs
                .iter()
                .filter(|definition| definition.name == "shared")
                .count(),
            1
        );
        let independent = flat
            .strat_defs
            .iter()
            .filter(|definition| definition.name == "twin")
            .collect::<Vec<_>>();
        assert_eq!(
            independent.len(),
            2,
            "text-identical definitions from independent modules remain distinct"
        );
        assert_ne!(independent[0].origin, independent[1].origin);
    }

    #[test]
    fn strategy_payload_follows_sum_rename_and_instantiation() {
        let (db, views, mut interner) = db_of(
            "smod STRAT-TRANSFORM-SOURCE is
               sort S .
               ops a b : -> S .
               op f : S -> S .
               var X : S .
               rl [step] : f(a) => b .
               strat go : S @ S .
               sd go(X) := match f(X) ; step .
             endsm
             smod STRAT-TRANSFORM-EXTRA is
               sort E .
               op e : -> E .
               strat extra : @ E .
               sd extra := idle .
             endsm
             smod STRAT-TRANSFORM-SUM is
               protecting STRAT-TRANSFORM-SOURCE + STRAT-TRANSFORM-EXTRA .
             endsm
             smod STRAT-TRANSFORM-RENAMED is
               protecting STRAT-TRANSFORM-SOURCE *
                 (sort S to T, op f to g, label step to moved) .
             endsm
             fth STRAT-TRANSFORM-THEORY is sort Elt . endfth
             smod STRAT-TRANSFORM-PARAM{P :: STRAT-TRANSFORM-THEORY} is
               var Y : P$Elt .
               strat keep : P$Elt @ P$Elt .
               sd keep(Y) := match Y .
             endsm
             fmod STRAT-TRANSFORM-TARGET is
               sort Elt .
               op x : -> Elt .
             endfm
             view STRAT-TRANSFORM-VIEW from STRAT-TRANSFORM-THEORY
               to STRAT-TRANSFORM-TARGET is
               sort Elt to Elt .
             endv
             smod STRAT-TRANSFORM-INSTANTIATED is
               protecting STRAT-TRANSFORM-PARAM{STRAT-TRANSFORM-VIEW} .
             endsm",
        );

        let sum = flatten("STRAT-TRANSFORM-SUM", &db, &views, &mut interner).expect("flatten sum");
        assert_eq!(
            sum.strat_decls
                .iter()
                .map(|declaration| declaration.name.as_str())
                .collect::<Vec<_>>(),
            ["go", "extra"]
        );

        let renamed =
            flatten("STRAT-TRANSFORM-RENAMED", &db, &views, &mut interner).expect("flatten rename");
        let declaration = renamed
            .strat_decls
            .iter()
            .find(|declaration| declaration.name == "go")
            .expect("renamed declaration");
        assert_eq!(declaration.domain, ["T"]);
        assert_eq!(declaration.subject, "T");
        let definition = renamed
            .strat_defs
            .iter()
            .find(|definition| definition.name == "go")
            .expect("renamed definition");
        assert_eq!(definition.home, None);
        assert!(
            definition.params[0]
                .iter()
                .any(|token| token.text(&interner) == "X"),
            "a declared variable that the result grammar binds at its renamed sort stays bare"
        );
        let StratExpr::Seq(test, application) = &definition.body else {
            panic!("expected nested test/application sequence");
        };
        let StratExpr::Test { pattern, .. } = &**test else {
            panic!("expected transformed test");
        };
        let pattern = pattern
            .iter()
            .map(|token| token.text(&interner))
            .collect::<Vec<_>>();
        assert!(pattern.contains(&"g"));
        assert!(pattern.contains(&"X"));
        assert!(!pattern.contains(&"f"));
        let StratExpr::Apply { label, .. } = &**application else {
            panic!("expected transformed application");
        };
        assert_eq!(label, "moved");

        let instantiated = flatten("STRAT-TRANSFORM-INSTANTIATED", &db, &views, &mut interner)
            .expect("flatten instantiation");
        let declaration = instantiated
            .strat_decls
            .iter()
            .find(|declaration| declaration.name == "keep")
            .expect("instantiated declaration");
        assert_eq!(declaration.domain, ["Elt"]);
        assert_eq!(declaration.subject, "Elt");
        let definition = instantiated
            .strat_defs
            .iter()
            .find(|definition| definition.name == "keep")
            .expect("instantiated definition");
        assert!(
            definition.params[0]
                .iter()
                .any(|token| token.text(&interner) == "Y:Elt")
        );
        let StratExpr::Test { pattern, .. } = &definition.body else {
            panic!("expected instantiated test");
        };
        assert!(pattern.iter().any(|token| token.text(&interner) == "Y:Elt"));
    }

    #[test]
    fn source_and_flat_strategy_payloads_remain_distinct() {
        let (db, views, mut interner) = db_of(
            "mod STRAT-PROJECTION-COMMON is sort S . op a : -> S . endm
             smod STRAT-PROJECTION-BASE is
               protecting STRAT-PROJECTION-COMMON .
               strat imported : @ S .
               sd imported := idle .
             endsm
             smod STRAT-PROJECTION-TOP is
               protecting STRAT-PROJECTION-BASE .
               strat local : @ S .
               sd local := idle .
             endsm",
        );
        let source = db.get("STRAT-PROJECTION-TOP").expect("source module");
        assert_eq!(
            source
                .strat_decls
                .iter()
                .map(|declaration| declaration.name.as_str())
                .collect::<Vec<_>>(),
            ["local"]
        );
        assert_eq!(
            source
                .strat_defs
                .iter()
                .map(|definition| definition.name.as_str())
                .collect::<Vec<_>>(),
            ["local"]
        );

        let flat = flatten("STRAT-PROJECTION-TOP", &db, &views, &mut interner)
            .expect("flatten projection");
        let declarations = flat
            .strat_decls
            .iter()
            .map(|declaration| declaration.name.as_str())
            .collect::<Vec<_>>();
        let definitions = flat
            .strat_defs
            .iter()
            .map(|definition| definition.name.as_str())
            .collect::<Vec<_>>();
        assert_eq!(declarations, ["local", "imported"]);
        assert_eq!(definitions, ["local", "imported"]);
    }

    /// Flattening records which statements an object module or theory declared, through plain and
    /// transitive imports, a renaming, an instantiation, and a parameter copy, in lockstep with the
    /// root-first statement order. A non-object root therefore completes exactly its imported
    /// object-module statements; an object root completes every statement.
    #[test]
    fn object_statements_follow_the_declaring_module() {
        let (mut db, views, mut interner) = db_of(
            "omod OBJ is
               sort V .
               op v : -> V [ctor] .
               class C | a : V .
               var X : Oid .
               rl [obj] : < X : C | a : v > => < X : C | a : v > .
             endom
             oth OTH is
               sort W .
               op w : -> W .
               class D | b : W .
               var Y : Oid .
               rl [oth] : < Y : D | b : w > => < Y : D | b : w > .
             endoth
             fth ELT is sort Elt . endfth
             omod BOX{X :: ELT} is
               class Box | e : X$Elt .
               var Z : Oid .
               rl [box] : < Z : Box | e : E:X$Elt > => < Z : Box | e : E:X$Elt > .
             endom
             fmod PLAIN is sort S . ops p q : -> S . eq [plain] : p = q . endfm
             view ToS from ELT to PLAIN is sort Elt to S . endv
             mod MID is protecting OBJ . endm
             mod USE{T :: OTH} is
               protecting MID .
               protecting OBJ * (class C to C2) .
               protecting BOX{ToS} .
               protecting PLAIN .
               sort U .
               ops u u' : -> U .
               eq [own] : u = u' .
             endm
             omod OROOT is protecting PLAIN . protecting OBJ .
             endom",
        );
        for name in ["OBJ", "OTH", "BOX"] {
            let imports = db.get(name).expect("object module").imports.clone();
            crate::prelude::ensure_builtins(&imports, &mut db, &mut interner);
        }
        let labelled = |pm: &PreModule| {
            assert_eq!(pm.object_statements.len(), pm.statements.len());
            pm.statements
                .iter()
                .enumerate()
                .filter_map(|(index, statement)| {
                    let (Statement::Eq { label, .. }
                    | Statement::Mb { label, .. }
                    | Statement::Rule { label, .. }) = statement;
                    label.clone().map(|label| {
                        (
                            label,
                            pm.object_statements[index],
                            pm.completes_object_patterns(index),
                        )
                    })
                })
                .collect::<Vec<_>>()
        };
        let entry =
            |label: &str, object: bool, completes: bool| (label.to_string(), object, completes);

        // Root-owned first, then the parameter copy, MID's OBJ, the renamed OBJ, and the instance, whose
        // view target PLAIN is collected before BOX's own statements.
        let flat = flatten("USE", &db, &views, &mut interner).expect("flatten USE");
        assert!(!flat.is_object);
        assert_eq!(
            labelled(&flat),
            [
                entry("own", false, false),
                entry("oth", true, true),
                entry("obj", true, true),
                entry("obj", true, true),
                entry("plain", false, false),
                entry("box", true, true),
            ]
        );

        let flat = flatten("OROOT", &db, &views, &mut interner).expect("flatten OROOT");
        assert_eq!(
            labelled(&flat),
            [entry("plain", false, true), entry("obj", true, true)]
        );

        // A transient root (META-LEVEL descent) keeps its own statements first, in lockstep.
        let mut transient = db.get("USE").expect("USE").clone();
        transient.params.clear();
        transient.imports.truncate(1);
        let flat = flatten_pre(&transient, &db, &views, &mut interner).expect("flatten_pre");
        assert_eq!(
            labelled(&flat),
            [entry("own", false, false), entry("obj", true, true)]
        );
        // An unflattened module records no provenance; its own orientation decides.
        let source = db.get("OBJ").expect("OBJ");
        assert!(source.object_statements.is_empty() && source.completes_object_patterns(0));
    }

    fn texts(bubble: &[Token], interner: &Interner) -> Vec<String> {
        bubble
            .iter()
            .map(|token| token.text(interner).to_string())
            .collect()
    }

    fn eq_sides(statement: &Statement, interner: &Interner) -> (Vec<String>, Vec<String>) {
        let Statement::Eq { lhs, rhs, .. } = statement else {
            panic!("expected an equation");
        };
        (texts(lhs, interner), texts(rhs, interner))
    }

    /// Statements of a renamed import keep their home variables. A name the importer's flattened grammar
    /// binds differently (`A`, redeclared by the importer) is inlined at its renamed home sort; a name it
    /// binds identically (`B`, the renamed alias itself) stays bare. A variable the home only sees through
    /// its own import (`Y`) is part of the home's scope too.
    #[test]
    fn renamed_import_inlines_only_rebound_home_variables() {
        let (db, views, mut i) = db_of(
            "fmod BASE is sort Tv . var Y : Tv . endfm\n\
             fmod HOME is\n\
               protecting BASE .\n\
               sort Nv . ops tt ff : -> Tv . op n : -> Nv .\n\
               op _&_ : Tv Tv -> Tv . op ok : Tv -> Tv . op id : Tv -> Tv .\n\
               vars A B : Tv .\n\
               eq tt & A = A .\n\
               eq ok(B) = tt .\n\
               eq id(Y) = Y .\n\
             endfm\n\
             fmod USER is\n\
               protecting HOME * (sort Tv to Truth) .\n\
               sort Other . var A : Nv . var Y : Other .\n\
             endfm\n",
        );
        let flat = flatten("USER", &db, &views, &mut i).expect("flatten");
        let sides: Vec<_> = flat.statements.iter().map(|st| eq_sides(st, &i)).collect();
        assert_eq!(sides.len(), 3, "{sides:?}");
        let (and_lhs, and_rhs) = &sides[0];
        assert!(and_lhs.contains(&"A:Truth".to_string()), "{and_lhs:?}");
        assert_eq!(and_rhs, &["A:Truth"]);
        let (ok_lhs, _) = &sides[1];
        assert!(ok_lhs.contains(&"B".to_string()), "{ok_lhs:?}");
        let (id_lhs, id_rhs) = &sides[2];
        assert!(id_lhs.contains(&"Y:Truth".to_string()), "{id_lhs:?}");
        assert_eq!(id_rhs, &["Y:Truth"]);
    }

    /// A parameter copy carries its theory closure's statements. The parameterized module's own `A` does
    /// not re-bind the copied import's `A`, and the copy's strategy definition keeps one spelling for its
    /// parameter and body.
    #[test]
    fn parameter_copy_inlines_rebound_home_variables() {
        let (db, views, mut i) = db_of(
            "smod TV is\n\
               sort Tv .\n\
               ops tt ff : -> Tv .\n\
               op _&_ : Tv Tv -> Tv .\n\
               var A : Tv .\n\
               eq tt & A = A .\n\
               strat keep : Tv @ Tv .\n\
               sd keep(A) := match A .\n\
             endsm\n\
             sth TH is\n\
               protecting TV .\n\
               sort Elt .\n\
             endsth\n\
             smod PM{X :: TH} is\n\
               sort Foo .\n\
               var A : Foo .\n\
             endsm\n",
        );
        let flat = flatten("PM", &db, &views, &mut i).expect("flatten");
        let sides: Vec<_> = flat.statements.iter().map(|st| eq_sides(st, &i)).collect();
        assert_eq!(sides.len(), 1, "{sides:?}");
        assert!(sides[0].0.contains(&"A:Tv".to_string()), "{sides:?}");
        assert_eq!(sides[0].1, ["A:Tv"]);
        let keep = flat
            .strat_defs
            .iter()
            .find(|definition| definition.name == "keep")
            .expect("copied definition");
        assert_eq!(texts(&keep.params[0], &i), ["A:Tv"]);
        let StratExpr::Test { pattern, .. } = &keep.body else {
            panic!("expected a test body");
        };
        assert_eq!(texts(pattern, &i), ["A:Tv"]);
    }

    /// A transient (reflected) module flattens the same way: an earlier sibling import's `Q : U` wins the
    /// name-deduplicated table, so the renamed import's `Q` is inlined at its home sort.
    #[test]
    fn transient_module_inlines_rebound_home_variables() {
        let (db, views, mut i) = db_of(
            "fmod TVM is sort Tv . ops tt ff : -> Tv . op n : -> Tv . op _&_ : Tv Tv -> Tv . \
             var Q : Tv . eq tt & Q = Q . endfm\n\
             fmod SIBM is sort U . var Q : U . endfm\n",
        );
        let toks = tokenize(
            "fmod TRANSIENT is including SIBM . including TVM * (op n to m) . endfm",
            &mut i,
        );
        let transient = Parser::new(&toks, &i)
            .parse_source()
            .expect("parse transient")
            .modules
            .remove(0);
        let flat = flatten_pre(&transient, &db, &views, &mut i).expect("flatten transient");
        let sides: Vec<_> = flat.statements.iter().map(|st| eq_sides(st, &i)).collect();
        assert_eq!(sides.len(), 1, "{sides:?}");
        assert!(sides[0].0.contains(&"Q:Tv".to_string()), "{sides:?}");
        assert_eq!(sides[0].1, ["Q:Tv"]);
    }

    /// A chain of 24 nested renamed imports, each level with its own variable `Yk : Sk`, under an importer
    /// that re-declares every nested level's variable. Each nested statement keeps its level's variable
    /// through all the enclosing bundles; the top level's statement keeps its home and its bare variable.
    /// Each bundle's root scope comes from the bundle itself, so the chain flattens in polynomial time;
    /// re-flattening each level's home inside every enclosing bundle doubled the work per level.
    #[test]
    fn nested_renaming_chain_keeps_each_level_variable() {
        const DEPTH: usize = 24;
        let mut src = String::from(
            "fmod M0 is sort S0 . ops a0 b0 : -> S0 . op f0 : S0 -> S0 . var Y0 : S0 . \
             eq f0(Y0) = a0 . endfm\n",
        );
        for k in 1..=DEPTH {
            let p = k - 1;
            src.push_str(&format!(
                "fmod M{k} is protecting M{p} * (op b{p} to c{p}) . sort S{k} . ops a{k} b{k} : -> S{k} . \
                 op f{k} : S{k} -> S{k} . var Y{k} : S{k} . eq f{k}(Y{k}) = a{k} . endfm\n"
            ));
        }
        let nested: Vec<String> = (0..DEPTH).map(|k| format!("Y{k}")).collect();
        src.push_str(&format!(
            "fmod TOP is protecting M{DEPTH} . sort T . vars {} : T . endfm\n",
            nested.join(" ")
        ));
        let (db, views, mut i) = db_of(&src);
        let flat = flatten("TOP", &db, &views, &mut i).expect("flatten");
        let sides: Vec<_> = flat.statements.iter().map(|st| eq_sides(st, &i)).collect();
        assert_eq!(sides.len(), DEPTH + 1, "{sides:?}");
        // Imports donate deepest first: levels 0..DEPTH-1 from the renamed bundles, then M{DEPTH}'s own.
        for (level, (lhs, _)) in sides.iter().enumerate() {
            let variable = if level < DEPTH {
                format!("Y{level}:S{level}")
            } else {
                format!("Y{level}")
            };
            assert!(lhs.contains(&variable), "level {level}: {lhs:?}");
        }
    }

    /// An alternating chain: each `Mk` renames `Wk-1`, which plainly imports `Mk-1`, with a statement and
    /// its own variable at every module. A renamed bundle's statements then also come from a home other
    /// than the bundle root (`Mk-1`). That home's scope is collected without scopes of its own, so the
    /// chain flattens in polynomial time, and every nested statement keeps its home variable under an
    /// importer re-declaring them all.
    #[test]
    fn alternating_renaming_chain_keeps_each_home_variable() {
        const DEPTH: usize = 16;
        let mut src = String::from(
            "fmod M0 is sort S0 . ops a0 b0 : -> S0 . op f0 : S0 -> S0 . var X0 : S0 . \
             eq f0(X0) = a0 . endfm\n",
        );
        for k in 1..=DEPTH {
            let p = k - 1;
            src.push_str(&format!(
                "fmod W{p} is protecting M{p} . op g{p} : S{p} -> S{p} . var Z{p} : S{p} . \
                 eq g{p}(Z{p}) = a{p} . endfm\n\
                 fmod M{k} is protecting W{p} * (op b{p} to c{p}) . sort S{k} . ops a{k} b{k} : -> S{k} . \
                 op f{k} : S{k} -> S{k} . var X{k} : S{k} . eq f{k}(X{k}) = a{k} . endfm\n"
            ));
        }
        let nested: Vec<String> = (0..DEPTH)
            .flat_map(|k| [format!("X{k}"), format!("Z{k}")])
            .collect();
        src.push_str(&format!(
            "fmod TOP is protecting M{DEPTH} . sort T . vars {} : T . endfm\n",
            nested.join(" ")
        ));
        let (db, views, mut i) = db_of(&src);
        let flat = flatten("TOP", &db, &views, &mut i).expect("flatten");
        let sides: Vec<_> = flat.statements.iter().map(|st| eq_sides(st, &i)).collect();
        assert_eq!(sides.len(), 2 * DEPTH + 1, "{sides:?}");
        for (lhs, _) in &sides {
            let (op, level) = lhs[0].split_at(1);
            let level: usize = level.parse().expect("level");
            let variable = match op {
                "f" if level == DEPTH => format!("X{level}"),
                "f" => format!("X{level}:S{level}"),
                _ => format!("Z{level}:S{level}"),
            };
            assert!(lhs.contains(&variable), "{lhs:?}");
        }
    }

    /// A renaming that turns a constant into the spelling of a home variable (`op n to m` with `var m`):
    /// the variable is inlined before renaming, so the renamed constant stays a constant, also once an
    /// enclosing renaming renames its sort (and sort-qualifies it, `( m ) .Truth`).
    #[test]
    fn renamed_constant_spelled_like_home_variable_stays_a_constant() {
        let (db, views, mut i) = db_of(
            "fmod H is sort Tv . ops n p : -> Tv . op f : Tv -> Tv . var m : Tv . eq f(m) = n . endfm\n\
             fmod R1 is protecting H * (op n to m) . endfm\n\
             fmod R2 is protecting R1 * (sort Tv to Truth) . endfm\n",
        );
        for (module, sort, constant) in [
            ("R1", "Tv", &["m"][..]),
            ("R2", "Truth", &["(", "m", ")", ".Truth"][..]),
        ] {
            let flat = flatten(module, &db, &views, &mut i).expect("flatten");
            let sides: Vec<_> = flat.statements.iter().map(|st| eq_sides(st, &i)).collect();
            assert_eq!(sides.len(), 1, "{module}: {sides:?}");
            let (lhs, rhs) = &sides[0];
            assert!(lhs.contains(&format!("m:{sort}")), "{module}: {lhs:?}");
            assert_eq!(rhs, constant, "{module}");
        }
    }

    /// An instantiated renamed module `(M * R){V}` donates its plain imports' statements without a home.
    /// The importer's own `A` does not re-bind the imported equation's `A`.
    #[test]
    fn instantiated_renamed_module_keeps_home_variables() {
        let (db, views, mut i) = db_of(
            "fmod TVB is sort Tv . ops tt ff : -> Tv . op _&_ : Tv Tv -> Tv . var A : Tv . \
             eq tt & A = A . endfm\n\
             fth T1 is sort Elt . endfth\n\
             fmod BOX{X :: T1} is protecting TVB . sort Box{X} . op box : X$Elt -> Box{X} . endfm\n\
             fmod ELT is sort E . op e : -> E . endfm\n\
             view VE from T1 to ELT is sort Elt to E . endv\n\
             fmod USE is protecting (BOX * (sort Box{X} to Crate{X})){VE} . sort Other . \
             var A : Other . endfm\n",
        );
        let flat = flatten("USE", &db, &views, &mut i).expect("flatten");
        let sides: Vec<_> = flat.statements.iter().map(|st| eq_sides(st, &i)).collect();
        assert_eq!(sides.len(), 1, "{sides:?}");
        assert!(sides[0].0.contains(&"A:Tv".to_string()), "{sides:?}");
        assert_eq!(sides[0].1, ["A:Tv"]);
    }
}
