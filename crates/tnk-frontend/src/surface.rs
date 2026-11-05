//! The surface layer: fixed top-level syntax for modules and commands, parsed by a
//! recursive-descent parser into a [`Source`](ast::Source) of [`PreModule`](ast::PreModule)s.
//! Term-carrying parts remain raw token bubbles until the per-module mixfix parse.

pub mod ast;
pub mod parser;
pub mod sort_spelling;
