pub mod spec;
pub mod bench;

#[forbid(unsafe_code)]
#[path = "../djinn/solution/mod.rs"]
pub mod solution;

pub use spec::{clamp, count_negative, min, run};
