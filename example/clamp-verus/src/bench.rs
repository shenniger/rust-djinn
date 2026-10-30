//! The performance workload for `cargo djinn optimize` / `cargo djinn bench`.
//! Human-written and trusted only for timing: correctness comes from the
//! verifier. It exercises the public stubs on representative inputs.

pub fn workload() {
    // a deterministic pseudo-random vector
    let mut x: u32 = 0x9E37_79B9;
    let mut v: Vec<i32> = Vec::with_capacity(4096);
    for _ in 0..4096 {
        x ^= x << 13;
        x ^= x >> 17;
        x ^= x << 5;
        v.push((x as i32) >> 4);
    }
    let mut acc: i64 = 0;
    for round in 0..64 {
        acc += crate::count_negative(&v) as i64;
        acc += crate::clamp(round - 32, -5, 5) as i64;
        acc += crate::min(round, 17) as i64;
    }
    std::hint::black_box(acc);
}
