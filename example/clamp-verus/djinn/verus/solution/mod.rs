//! LLM-owned: the implementation of the `func`s of the specification, inside `verus! { … }`.
use vstd::prelude::*;

verus! {

pub fn clamp(x: i32, lo: i32, hi: i32) -> (r: i32)
    requires
        lo <= hi,
    ensures
        lo <= r <= hi,
        x < lo ==> r == lo,
        x > hi ==> r == hi,
        lo <= x <= hi ==> r == x,
{
    if x < lo { lo } else if x > hi { hi } else { x }
}

pub fn count_negative(v: &[i32]) -> (r: usize)
    ensures
        r as int == v@.filter(|y: i32| (y as int) < 0).len() as int,
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    proof {
        reveal(Seq::filter);
        assert(v@.subrange(0, 0) =~= Seq::<i32>::empty());
    }
    while i < v.len()
        invariant
            i <= v.len(),
            count <= i,
            count as int == v@.subrange(0, i as int).filter(|y: i32| (y as int) < 0).len() as int,
        decreases v.len() - i,
    {
        proof {
            reveal(Seq::filter);
            let p = |y: i32| (y as int) < 0;
            let s = v@.subrange(0, i as int);
            let t = v@.subrange(0, i as int + 1);
            assert(t =~= s.push(v@[i as int]));
            assert(t.drop_last() =~= s);
            assert(t.last() == v@[i as int]);
        }
        if v[i] < 0 {
            count = count + 1;
        }
        i = i + 1;
    }
    proof {
        assert(v@.subrange(0, v@.len() as int) =~= v@);
    }
    count
}

pub fn min(a: i32, b: i32) -> (r: i32)
    ensures
        r <= a,
        r <= b,
        r == a || r == b,
{
    if a <= b { a } else { b }
}

pub fn max(a: i32, b: i32) -> (r: i32)
    ensures
        r >= a,
        r >= b,
        r == a || r == b,
{
    if a >= b { a } else { b }
}

} // verus!
