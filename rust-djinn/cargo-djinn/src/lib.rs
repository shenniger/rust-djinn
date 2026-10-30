//! The Djinn driver (Lean/Aeneas and Verus backends) as a library: used by the `cargo-djinn` binary
//! and by `rust-djinn-lsp`.

pub mod agent;
pub mod bench;
pub mod config;
pub mod guide;
pub mod guide_verus;
pub mod jail;
pub mod mcp;
pub mod models;
pub mod optimize;
pub mod smoke;
pub mod status;
pub mod verify;
pub mod verify_verus;
