// Written by `cargo djinn translate`: rebuild (and so rerun the djinn build
// gate) when a file is added under the solution or the proofs.
fn main() {
    println!("cargo:rerun-if-changed=djinn/solution");
    println!("cargo:rerun-if-changed=djinn/proofs/ClampDemo");
}
