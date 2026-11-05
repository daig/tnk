//! View storage and signature validation.
//!
//! A view maps a source theory to a target module or theory for use in parameterized instantiation.
//! Validation checks sort existence, connected-component preservation, and source/target operator
//! profiles. Theory axioms remain proof obligations rather than executable validation tests.

use std::collections::{HashMap, HashSet};
use tnk_core::sort::SortId;
use tnk_frontend::lex::{Interner, Token};
use tnk_frontend::load::{build_loaded_module_with_host_functions, build_logic_command_parses};
use tnk_frontend::sig::syntax::{BuiltModule, OpProfile};
use tnk_frontend::surface::ast::{ModuleExpr, OpMap, VarDecl, ViewDecl};
use tnk_frontend::surface::sort_spelling::{kind_components, kind_representative};

use crate::db::ModuleDb;
use crate::flatten::flatten;

/// A name → [`ViewDecl`] table — the parsed, validated views of a program.
#[derive(Debug, Default, Clone)]
pub struct ViewDb {
    views: HashMap<String, ViewDecl>,
}

impl ViewDb {
    pub fn new() -> Self {
        Self::default()
    }

    /// Insert a view (overwriting any previous view of the same name).
    pub fn insert(&mut self, v: ViewDecl) {
        self.views.insert(v.name.clone(), v);
    }

    pub fn get(&self, name: &str) -> Option<&ViewDecl> {
        self.views.get(name)
    }

    pub fn contains(&self, name: &str) -> bool {
        self.views.contains_key(name)
    }
}

/// Extract the named base of a plain or instantiated view endpoint. Sum and renaming endpoints are not
/// accepted by view validation.
fn expr_base_name(e: &ModuleExpr) -> Result<&str, String> {
    match e {
        ModuleExpr::Named(n) => Ok(n),
        ModuleExpr::Instantiation(base, _) => expr_base_name(base),
        _ => Err("a view's `from`/`to` must be a named module/theory or an instantiation".into()),
    }
}

#[derive(Clone)]
enum OpMapTarget {
    Op(String),
    Term(Vec<Token>),
}

#[derive(Clone)]
struct OpMapSpec {
    source: String,
    dom_range: Option<(Vec<String>, String)>,
    target: OpMapTarget,
}

fn canonical_tokens(tokens: &[Token], interner: &Interner) -> String {
    tokens
        .iter()
        .map(|token| interner.resolve(token.sym))
        .collect()
}

/// Recover the canonical source operator name from an op-map source. Op→op maps carry just the name;
/// op→term maps may carry a prefix or mixfix application whose variable positions denote holes.
fn map_source_name(
    v: &ViewDecl,
    tokens: &[Token],
    interner: &Interner,
    source: &BuiltModule,
) -> String {
    if tokens.len() >= 3 && interner.resolve(tokens[1].sym) == "(" {
        return interner.resolve(tokens[0].sym).to_string();
    }
    let variables: HashSet<&str> = v
        .vars
        .iter()
        .flat_map(|decl| decl.names.iter().map(String::as_str))
        .collect();
    tokens
        .iter()
        .map(|token| {
            let text = interner.resolve(token.sym);
            let (base, qualified) = text.rsplit_once(':').map_or((text, false), |(name, ty)| {
                (name, !name.is_empty() && source_type_name(source, ty))
            });
            if variables.contains(base) || qualified {
                "_"
            } else {
                text
            }
        })
        .collect()
}

/// Whether a colon suffix denotes a source sort or kind. A colon inside an operator token is not enough
/// to make that token a variable (`marker:tag` may be a declared constant).
fn source_type_name(source: &BuiltModule, name: &str) -> bool {
    selector_sort(source, name).is_some()
}

fn op_map_specs(v: &ViewDecl, interner: &Interner, source: &BuiltModule) -> Vec<OpMapSpec> {
    v.op_maps
        .iter()
        .map(|mapping| match mapping {
            OpMap::Op {
                from,
                to,
                dom_range,
            } => OpMapSpec {
                source: canonical_tokens(from, interner),
                dom_range: dom_range.clone(),
                target: OpMapTarget::Op(canonical_tokens(to, interner)),
            },
            OpMap::Term {
                from,
                to,
                dom_range,
            } => OpMapSpec {
                source: map_source_name(v, from, interner, source),
                dom_range: dom_range.clone(),
                target: OpMapTarget::Term(to.clone()),
            },
        })
        .collect()
}

fn selector_matches(
    profile: &OpProfile,
    selector: &(Vec<String>, String),
    source: &BuiltModule,
) -> bool {
    selector.0.len() == profile.domain.len()
        && selector
            .0
            .iter()
            .zip(&profile.domain)
            .all(|(name, &resolved)| {
                selector_sort(source, name).is_some_and(|declared| {
                    source.engine.sorts().kind_of(declared)
                        == source.engine.sorts().kind_of(resolved)
                })
            })
        && selector_sort(source, &selector.1).is_some_and(|range| {
            source.engine.sorts().kind_of(range) == source.engine.sorts().kind_of(profile.range)
        })
}

/// The source sort through which a written sort spelling names its kind: the sort itself, or the first
/// component of a kind spelling (`op f : [Elt] -> [Elt] to g`), the component through which declarations
/// resolve a kind.
fn selector_sort(source: &BuiltModule, name: &str) -> Option<SortId> {
    source.sorts.get(kind_representative(name)).copied()
}

fn mapped_sort(
    source_sort: SortId,
    source: &BuiltModule,
    target: &BuiltModule,
    sort_image: &HashMap<String, String>,
) -> Option<SortId> {
    let source_sorts = source.engine.sorts();
    if source_sorts.sort(source_sort).is_error {
        let member = source_sorts
            .kind(source_sorts.kind_of(source_sort))
            .members
            .first()
            .copied()?;
        let image = sort_image.get(source_sorts.name(member))?;
        let target_member = *target.sorts.get(image)?;
        Some(
            target
                .engine
                .sorts()
                .error_sort(target.engine.sorts().kind_of(target_member)),
        )
    } else {
        sort_image
            .get(source_sorts.name(source_sort))
            .and_then(|name| target.sorts.get(name))
            .copied()
    }
}

fn profile_name<'a>(profile: &OpProfile, module: &'a BuiltModule) -> &'a str {
    module.engine.symbol(profile.symbol).name()
}

fn profile_text(profile: &OpProfile, module: &BuiltModule) -> String {
    let domain = profile
        .domain
        .iter()
        .map(|&sort| module.engine.sorts().name(sort))
        .collect::<Vec<_>>()
        .join(" ");
    format!(
        "{} : {} -> {}",
        profile_name(profile, module),
        domain,
        module.engine.sorts().name(profile.range)
    )
}

/// Validate a view's signature homomorphism before storage or instantiation.
pub fn validate_view(
    v: &ViewDecl,
    db: &ModuleDb,
    views: &ViewDb,
    interner: &mut Interner,
) -> Result<(), String> {
    validate_view_with_host_functions(
        v,
        db,
        views,
        interner,
        &tnk_core::host::HostFunctionCatalog::default(),
    )
}

/// Validate a view while resolving any strict host attachments against `host_functions`.
pub fn validate_view_with_host_functions(
    v: &ViewDecl,
    db: &ModuleDb,
    views: &ViewDb,
    interner: &mut Interner,
    host_functions: &tnk_core::host::HostFunctionCatalog,
) -> Result<(), String> {
    let from_name = expr_base_name(&v.from)?;
    let to_name = expr_base_name(&v.to)?;

    let from_pm = db.get(from_name).ok_or_else(|| {
        format!(
            "view `{}`: source theory `{from_name}` is not defined",
            v.name
        )
    })?;
    if !from_pm.is_theory {
        return Err(format!(
            "view `{}`: source `{from_name}` is not a theory",
            v.name
        ));
    }
    db.get(to_name).ok_or_else(|| {
        format!(
            "view `{}`: target module `{to_name}` is not defined",
            v.name
        )
    })?;

    // Use the accumulated view table because the source may depend on an earlier instantiation.
    let from_flat = flatten(from_name, db, views, interner)?;
    let from_sorts: HashSet<&str> = from_flat.sorts.iter().map(String::as_str).collect();

    for (source, _) in &v.sort_maps {
        if !from_sorts.contains(source.as_str()) {
            return Err(format!(
                "view `{}`: sort `{source}` is not a sort of `{from_name}`",
                v.name
            ));
        }
    }

    // A parameterized view's target contains its own free parameters and is checked when instantiated.
    // A plain target is fully checkable now.
    if !v.params.is_empty() || !matches!(&v.to, ModuleExpr::Named(_)) {
        return Ok(());
    }

    let to_flat = flatten(to_name, db, views, interner)?;
    let to_sorts: HashSet<&str> = to_flat.sorts.iter().map(String::as_str).collect();
    let explicit: HashMap<&str, &str> = v
        .sort_maps
        .iter()
        .map(|(source, target)| (source.as_str(), target.as_str()))
        .collect();
    let mut sort_image = HashMap::new();
    for source in &from_flat.sorts {
        let target = explicit
            .get(source.as_str())
            .copied()
            .unwrap_or(source.as_str());
        if !to_sorts.contains(target) {
            return Err(format!(
                "view `{}`: failed to find sort {target} in {to_name} to represent sort {source} from {from_name}",
                v.name
            ));
        }
        sort_image.insert(source.clone(), target.to_string());
    }

    let source =
        build_loaded_module_with_host_functions(&from_flat, interner, host_functions)?.built;
    let target = build_loaded_module_with_host_functions(&to_flat, interner, host_functions)?.built;

    // A sort map is a homomorphism of the order-sorted signature: connected source sorts stay connected.
    for (index, left_name) in from_flat.sorts.iter().enumerate() {
        let left = source.sorts[left_name];
        let left_image = target.sorts[&sort_image[left_name]];
        for right_name in &from_flat.sorts[index + 1..] {
            let right = source.sorts[right_name];
            if source.engine.sorts().same_kind(left, right) {
                let right_image = target.sorts[&sort_image[right_name]];
                if !target.engine.sorts().same_kind(left_image, right_image) {
                    return Err(format!(
                        "view `{}`: sorts {left_name} and {right_name} from {from_name} are in the same kind, \
                         but {} and {} in {to_name} are in different kinds",
                        v.name, sort_image[left_name], sort_image[right_name]
                    ));
                }
            }
        }
    }

    let maps = op_map_specs(v, interner, &source);
    // Every explicit source must resolve; a signature selector chooses one connected-component profile.
    for mapping in &maps {
        let found = source.op_profiles.iter().any(|profile| {
            profile_name(profile, &source) == mapping.source
                && mapping
                    .dom_range
                    .as_ref()
                    .is_none_or(|selector| selector_matches(profile, selector, &source))
        });
        if !found {
            return Err(format!(
                "view `{}`: source operator `{}` is not defined in {from_name}",
                v.name, mapping.source
            ));
        }
    }

    let mut term_target = if maps
        .iter()
        .any(|mapping| matches!(mapping.target, OpMapTarget::Term(_)))
    {
        let mut term_pm = to_flat.clone();
        term_pm.statements.clear();
        term_pm.strat_defs.clear();
        for variable in &v.vars {
            // A kind-sorted view variable (`var Z : [Elt]`) takes the kind of its components' images.
            let target_sort = match kind_components(&variable.sort) {
                None => sort_image.get(&variable.sort).cloned(),
                Some(components) => components
                    .iter()
                    .map(|component| sort_image.get(*component).cloned())
                    .collect::<Option<Vec<_>>>()
                    .map(|images| format!("[{}]", images.join(","))),
            }
            .ok_or_else(|| {
                format!(
                    "view `{}`: variable sort `{}` is not a source theory sort",
                    v.name, variable.sort
                )
            })?;
            term_pm.vars.push(VarDecl {
                names: variable.names.clone(),
                sort: target_sort,
            });
        }
        Some(build_loaded_module_with_host_functions(
            &term_pm,
            interner,
            host_functions,
        )?)
    } else {
        None
    };

    for source_profile in &source.op_profiles {
        let source_name = profile_name(source_profile, &source);
        let exact = maps.iter().find(|mapping| {
            mapping.source == source_name
                && mapping
                    .dom_range
                    .as_ref()
                    .is_some_and(|selector| selector_matches(source_profile, selector, &source))
        });
        let generic = maps
            .iter()
            .find(|mapping| mapping.source == source_name && mapping.dom_range.is_none());
        let mapping = exact.or(generic);
        let target_map = mapping.map(|mapping| &mapping.target);
        let Some(mapped_domain): Option<Vec<SortId>> = source_profile
            .domain
            .iter()
            .map(|&sort| mapped_sort(sort, &source, &target, &sort_image))
            .collect()
        else {
            return Err(format!(
                "view `{}`: could not map the domain of source operator {}",
                v.name,
                profile_text(source_profile, &source)
            ));
        };
        let Some(mapped_range) = mapped_sort(source_profile.range, &source, &target, &sort_image)
        else {
            return Err(format!(
                "view `{}`: could not map the range of source operator {}",
                v.name,
                profile_text(source_profile, &source)
            ));
        };
        if let Some(OpMapTarget::Term(tokens)) = target_map {
            let term_module = term_target
                .as_mut()
                .expect("term-map target module built above");
            let parses =
                build_logic_command_parses(term_module, interner, tokens).map_err(|error| {
                    format!(
                        "view `{}`: target term for operator {} does not parse in {to_name}: {error}",
                        v.name,
                        profile_text(source_profile, &source)
                    )
                })?;
            let suitable = parses.iter().any(|(_, _, dag)| {
                let sort = term_module.built.engine.sort_of(*dag);
                term_module.built.engine.sorts().leq(sort, mapped_range)
            });
            if !suitable {
                return Err(format!(
                    "view `{}`: target term for operator {} does not have a sort below {} in {to_name}",
                    v.name,
                    profile_text(source_profile, &source),
                    target.engine.sorts().name(mapped_range)
                ));
            }
            continue;
        }
        let target_name = match target_map {
            Some(OpMapTarget::Op(name)) => name.as_str(),
            Some(OpMapTarget::Term(_)) => unreachable!(),
            None => source_name,
        };
        let suitable = target.op_profiles.iter().any(|profile| {
            profile_name(profile, &target) == target_name
                && profile.domain.len() == mapped_domain.len()
                && mapped_domain
                    .iter()
                    .zip(&profile.domain)
                    .all(|(&image, &domain)| target.engine.sorts().leq(image, domain))
                && target.engine.sorts().leq(profile.range, mapped_range)
        });
        if !suitable {
            return Err(format!(
                "view `{}`: failed to find suitable operator {target_name} in {to_name} to represent \
                 operator {} from {from_name}",
                v.name,
                profile_text(source_profile, &source)
            ));
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use tnk_frontend::lex::tokenize;
    use tnk_frontend::surface::parser::Parser;

    /// Parse a source into (module DB, views, interner).
    fn setup(src: &str) -> (ModuleDb, Vec<ViewDecl>, Interner) {
        let mut i = Interner::new();
        let toks = tokenize(src, &mut i);
        let s = Parser::new(&toks, &i).parse_source().expect("parse");
        (ModuleDb::from_modules(s.modules), s.views, i)
    }

    /// A well-formed view (`Elt` mapped to an existing target sort) validates.
    #[test]
    fn good_view_validates() {
        let (db, views, mut i) = setup(
            "fth TRIV is sort Elt . endfth\n\
             fmod NUM is sort N . op z : -> N [ctor] . endfm\n\
             view ToNum from TRIV to NUM is sort Elt to N . endv\n",
        );
        assert!(validate_view(&views[0], &db, &ViewDb::new(), &mut i).is_ok());
    }

    /// Mapping a theory sort to a missing target sort reports both the sort and target module.
    #[test]
    fn missing_target_sort_rejected() {
        let (db, views, mut i) = setup(
            "fth TRIV is sort Elt . endfth\n\
             fmod NUM is sort N . op z : -> N [ctor] . endfm\n\
             view Bad from TRIV to NUM is sort Elt to NoSuch . endv\n",
        );
        let err = validate_view(&views[0], &db, &ViewDb::new(), &mut i).unwrap_err();
        assert!(
            err.contains("failed to find sort NoSuch in NUM"),
            "got: {err}"
        );
    }

    /// A view whose source is not a theory is rejected.
    #[test]
    fn non_theory_source_rejected() {
        let (db, views, mut i) = setup(
            "fmod A is sort Elt . endfm\n\
             fmod NUM is sort N . endfm\n\
             view V from A to NUM is sort Elt to N . endv\n",
        );
        let err = validate_view(&views[0], &db, &ViewDb::new(), &mut i).unwrap_err();
        assert!(err.contains("is not a theory"), "got: {err}");
    }

    /// An unmapped theory sort defaults to identity and must exist in the target.
    #[test]
    fn unmapped_theory_sort_must_exist_in_target() {
        // The theory declares `Elt` and `Key`; the view maps only `Elt`, so `Key` defaults to identity —
        // absent from NUM ⇒ rejected.
        let (db, views, mut i) = setup(
            "fth TWO is sorts Elt Key . endfth\n\
             fmod NUM is sort N . endfm\n\
             view V from TWO to NUM is sort Elt to N . endv\n",
        );
        let err = validate_view(&views[0], &db, &ViewDb::new(), &mut i).unwrap_err();
        assert!(err.contains("failed to find sort Key in NUM"), "got: {err}");
    }
    #[test]
    fn connected_component_split_rejected() {
        let (db, views, mut i) = setup(
            "fth T is sorts A B . subsort A < B . endfth\n\
             fmod M is sorts X Y . endfm\n\
             view V from T to M is sort A to X . sort B to Y . endv\n",
        );
        let err = validate_view(&views[0], &db, &ViewDb::new(), &mut i).unwrap_err();
        assert!(err.contains("in different kinds"), "got: {err}");
    }

    #[test]
    fn nonpreserving_subsort_map_remains_usable() {
        let (db, views, mut i) = setup(
            "fth T is sorts A B . subsort A < B . endfth\n\
             fmod M is sorts X Y Top . subsorts X Y < Top . endfm\n\
             view V from T to M is sort A to X . sort B to Y . endv\n",
        );
        assert!(
            validate_view(&views[0], &db, &ViewDb::new(), &mut i).is_ok(),
            "missing subsort images remain usable"
        );
    }

    #[test]
    fn incompatible_operator_profile_rejected() {
        let (db, views, mut i) = setup(
            "fth T is sort E . op f : E -> E . endfth\n\
             fmod M is sort S . op g : S S -> S . endfm\n\
             view V from T to M is sort E to S . op f to g . endv\n",
        );
        let err = validate_view(&views[0], &db, &ViewDb::new(), &mut i).unwrap_err();
        assert!(
            err.contains("failed to find suitable operator g"),
            "got: {err}"
        );
    }

    #[test]
    fn operator_to_term_range_rejected() {
        let (db, views, mut i) = setup(
            "fth T is sort E . op f : E -> E . endfth\n\
             fmod M is sorts S Other . op other : -> Other . endfm\n\
             view V from T to M is\n\
               sort E to S .\n\
               op f(X:E) to term other .\n\
             endv\n",
        );
        let err = validate_view(&views[0], &db, &ViewDb::new(), &mut i).unwrap_err();
        assert!(err.contains("does not have a sort below S"), "got: {err}");
    }

    /// An operator-map selector may spell its sorts as kinds (Appendix D `OpSelector`), over a source
    /// operator declared at the kind or at a sort of it. A kind of no source sort still selects nothing.
    #[test]
    fn kind_spelled_selector_validates() {
        let (db, views, mut i) = setup(
            "fth T is sort E . op f : [E] -> [E] . op k : E E -> E . endfth\n\
             fmod M is sort S . op g : [S] -> [S] . op k2 : S S -> S . endfm\n\
             view V from T to M is\n\
               sort E to S .\n\
               op f : [E] -> [E] to g .\n\
               op k : [E] E -> [E] to k2 .\n\
             endv\n\
             view Bad from T to M is sort E to S . op f : [Nope] -> [E] to g . endv\n",
        );
        assert_eq!(
            validate_view(&views[0], &db, &ViewDb::new(), &mut i),
            Ok(())
        );
        let err = validate_view(&views[1], &db, &ViewDb::new(), &mut i).unwrap_err();
        assert!(
            err.contains("source operator `f` is not defined"),
            "got: {err}"
        );
    }

    /// A view variable declared at a kind takes the kind of its sort image in the target, so an
    /// operator-to-term map can use it where the target operator expects that kind.
    #[test]
    fn kind_sorted_view_variable_validates() {
        let (db, views, mut i) = setup(
            "fth T is sort E . op f : E -> E . endfth\n\
             fmod M is sort S . op g : [S] -> S . endfm\n\
             view V from T to M is sort E to S . var Z : [E] . op f(Z) to term g(Z) . endv\n\
             view Bad from T to M is sort E to S . var Z : [Nope] . op f(Z) to term g(Z) . endv\n",
        );
        assert_eq!(
            validate_view(&views[0], &db, &ViewDb::new(), &mut i),
            Ok(())
        );
        let err = validate_view(&views[1], &db, &ViewDb::new(), &mut i).unwrap_err();
        assert!(
            err.contains("variable sort `[Nope]` is not a source theory sort"),
            "got: {err}"
        );
    }
}
