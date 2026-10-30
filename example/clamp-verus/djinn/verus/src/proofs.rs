//! The implementer's file. Written once by `cargo djinn translate`, never
//! overwritten. Fill in every `proof fn` (replace the TODO marker with a proof);
//! add any helper lemmas you need in this file, or in modules under `proofs/`
//! (`mod helper;` here loads `proofs/helper.rs`).
#![allow(unused_imports, unused_variables, unused_parens, non_snake_case, dead_code)]
use vstd::prelude::*;
use crate::relations::*;
use crate::vocab::*;

verus! {

// ---- clamp (edited in the jail)

pub proof fn clamp_unambiguous(x: i32, lo: i32, hi: i32, o1: i32, o2: i32)
    requires
        clamp_spec(x, lo, hi, o1),
        clamp_spec(x, lo, hi, o2),
    ensures
        o1 == o2,
{
    // TODO(implementer): prove this; an empty body does not verify
}

// ---- count_negative

pub proof fn count_negative_unambiguous(v: Seq<i32>, o1: usize, o2: usize)
    requires
        count_negative_spec(v, o1),
        count_negative_spec(v, o2),
    ensures
        o1 == o2,
{
    // TODO(implementer): prove this; an empty body does not verify
}

// ---- min

pub proof fn min_unambiguous(a: i32, b: i32, o1: i32, o2: i32)
    requires
        min_spec(a, b, o1),
        min_spec(a, b, o2),
    ensures
        o1 == o2,
{
    // TODO(implementer): prove this; an empty body does not verify
}

// ---- max

pub proof fn max_unambiguous(a: i32, b: i32, o1: i32, o2: i32)
    requires
        max_spec(a, b, o1),
        max_spec(a, b, o2),
    ensures
        o1 == o2,
{
    // TODO(implementer): prove this; an empty body does not verify
}

} // verus!
