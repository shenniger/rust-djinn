//! Djinn: write specifications only, as Rust macros. An LLM implements them
//! in a `solution` module and proves them in Lean against the Aeneas model.
//!
//! ```ignore
//! djinn::djinn! {
//!     #[total]
//!     pub rel perm(list: &[i32]) -> t: Vec<i32> { … }
//!
//!     #[requires(!list.is_empty())]
//!     pub fn max(list: &[i32]) -> r: i32 {
//!         r in list;
//!         for x in list { x <= r }
//!     }
//! }
//! ```
//!
//! A `fn` expands to a delegation stub `pub fn max(list: &[i32]) -> i32 {
//! crate::solution::max(list) }`; a `rel` expands to nothing executable.
//! The constraint language is documented in DESIGN.md. Lean obligations
//! are produced by `cargo djinn`, not by these macros. `func!` and `rel!`
//! remain as single-item forms.
pub use djinn_macros::{djinn, func, rel, solution};
