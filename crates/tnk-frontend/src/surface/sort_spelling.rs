//! Canonical sort spellings as produced by the surface parser: a sort name (`Nat`), a structured sort
//! (`Map{X,Y}`), or a **kind** spelling (`[A]`, `[A,B]`) whose components are complete sort spellings.
//!
//! A kind spelling names the connected component (TNK-SORT-002) of its sorts, so every module-algebra
//! transformation that rewrites sort names (renaming, parameter copies, instantiation, view sort images)
//! must rewrite each component rather than treat the bracket text as one opaque sort name, and every
//! lookup that resolves a written sort to its component must resolve a kind through one component.

/// The depth-0 comma components of a kind spelling (`[A,Map{X,Y}]` gives `A` and `Map{X,Y}`), or `None`
/// when `name` is not bracketed. Brace and bracket nesting keep structured components intact; blanks
/// around a component are not part of it.
pub fn kind_components(name: &str) -> Option<Vec<&str>> {
    let inner = name.strip_prefix('[')?.strip_suffix(']')?;
    let mut parts = Vec::new();
    let mut depth = 0usize;
    let mut start = 0;
    for (index, c) in inner.char_indices() {
        match c {
            '{' | '[' => depth += 1,
            '}' | ']' => depth = depth.saturating_sub(1),
            ',' if depth == 0 => {
                parts.push(inner[start..index].trim());
                start = index + 1;
            }
            _ => {}
        }
    }
    parts.push(inner[start..].trim());
    Some(parts)
}

/// The sort through which `name` resolves to a connected component: the first component of a kind
/// spelling, or `name` itself for a sort spelling.
pub fn kind_representative(name: &str) -> &str {
    kind_components(name)
        .and_then(|parts| parts.first().copied())
        .unwrap_or(name)
}

/// Rewrite the sort names inside one sort spelling. A sort spelling is passed to `map` whole; a kind
/// spelling has each component passed separately and is reassembled in canonical no-space form. `map`
/// returns `None` for an unchanged name. The result is `None` when no name changed.
pub fn map_sort_spelling(
    name: &str,
    mut map: impl FnMut(&str) -> Option<String>,
) -> Option<String> {
    let Some(parts) = kind_components(name) else {
        return map(name);
    };
    let mut changed = false;
    let mapped: Vec<String> = parts
        .iter()
        .map(|part| match map(part) {
            Some(target) => {
                changed = true;
                target
            }
            None => (*part).to_string(),
        })
        .collect();
    changed.then(|| format!("[{}]", mapped.join(",")))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn kind_components_split_at_depth_zero_only() {
        assert_eq!(kind_components("Nat"), None);
        assert_eq!(kind_components("List{Nat}"), None);
        assert_eq!(kind_components("[Nat]"), Some(vec!["Nat"]));
        assert_eq!(kind_components("[A,B]"), Some(vec!["A", "B"]));
        assert_eq!(
            kind_components("[Map{X,Y},S{X}]"),
            Some(vec!["Map{X,Y}", "S{X}"])
        );
        assert_eq!(kind_components("[X$Elt,S{X}]"), Some(vec!["X$Elt", "S{X}"]));
    }

    #[test]
    fn representative_is_first_component() {
        assert_eq!(kind_representative("Nat"), "Nat");
        assert_eq!(kind_representative("[Q,R]"), "Q");
        assert_eq!(kind_representative("[Map{X,Y}]"), "Map{X,Y}");
        assert_eq!(kind_representative("[Map{X,Y},Q]"), "Map{X,Y}");
    }

    #[test]
    fn map_rewrites_each_component() {
        let rename = |s: &str| (s == "P").then(|| "PX".to_string());
        assert_eq!(map_sort_spelling("P", rename), Some("PX".into()));
        assert_eq!(map_sort_spelling("[P]", rename), Some("[PX]".into()));
        assert_eq!(map_sort_spelling("[Q,P]", rename), Some("[Q,PX]".into()));
        assert_eq!(map_sort_spelling("[Q]", rename), None);
        assert_eq!(map_sort_spelling("Q", rename), None);
    }
}
