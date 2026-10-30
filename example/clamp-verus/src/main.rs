//! `printf '3\n-4\n12\n' | cargo run -- 0 10`: the driver lives next to the specification (`spec.rs`).
use std::io::Read;

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let (lo, hi) = match (args.first().and_then(|a| a.parse().ok()), args.get(1).and_then(|a| a.parse().ok())) {
        (Some(lo), Some(hi)) => (lo, hi),
        _ => {
            eprintln!("usage: clampdemo <lo> <hi>  (integers on stdin, one per line)");
            std::process::exit(2);
        }
    };
    let mut input = String::new();
    let _ = std::io::stdin().read_to_string(&mut input);
    match clampdemo::run(&input, lo, hi) {
        Ok(report) => println!("{report}"),
        Err(e) => {
            eprintln!("{e}");
            std::process::exit(2);
        }
    }
}
