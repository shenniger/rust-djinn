//! A small specification for trying the implementer harness.

use djinn::djinn;

djinn! {
    #[requires(lo <= hi)]
    pub fn clamp(x: i32, lo: i32, hi: i32) -> r: i32 {
        lo <= r <= hi;
        x < lo => r == lo;
        x > hi => r == hi;
        lo <= x <= hi => r == x;
    }

    pub fn count_negative(v: &[i32]) -> r: usize {
        r == v.iter().filter(|y| y < 0).count();
    }

    pub fn min(a: i32, b: i32) -> r: i32 {
        r <= a;
        r <= b;
        r == a || r == b;
    }

    pub fn max(a: i32, b: i32) -> r: i32 {
        r >= a;
        r >= b;
        r == a || r == b;
    }
}

// ------------------------------------------------------------------ a driver
//
// Plain Rust beside the specification: it parses text, calls the verified
// functions and formats the result. Charon never reaches it (translation
// starts from the `fn`s above), so `String` and `format!` are fine here.
// `clamp` requires `lo <= hi`; the driver checks that before calling it.

/// Reads one integer per line, clamps each into `[lo, hi]`, and reports how
/// many of the inputs were negative and the smallest clamped value.
pub fn run(input: &str, lo: i32, hi: i32) -> Result<String, String> {
    if lo > hi {
        return Err(format!("empty range: lo = {lo} > hi = {hi}"));
    }
    let mut values: Vec<i32> = Vec::new();
    for line in input.lines().map(str::trim).filter(|l| !l.is_empty()) {
        values.push(line.parse().map_err(|_| format!("not an integer: `{line}`"))?);
    }
    let negatives = count_negative(&values);
    let clamped: Vec<i32> = values.iter().map(|&x| clamp(x, lo, hi)).collect();
    let smallest = clamped.iter().copied().reduce(min);
    Ok(format!("{negatives} negative input(s); clamped to [{lo}, {hi}]: {clamped:?}; smallest: {smallest:?}"))
}
