//! Trusted Lean models for the standard-library items Aeneas has no model
//! of but Djinn supports: `String` (as its UTF-8 bytes) and `HashMap` (as an
//! association list), plus the hashing and conversion items their use drags
//! in, `memchr`, and the integer bit-counting methods (`count_ones` and kin,
//! on Lean core's `BitVec.cpop` / `ctz` / `clz`). Aeneas lists what it could not model in `*External_Template.lean`
//! (one `Name pattern` per item, with the exact Lean signature it expects);
//! when every listed item is covered here, `verify` writes
//! `FunsExternal.lean` / `TypesExternal.lean` from this library and goes on;
//! anything uncovered is a failure with an explanation (DESIGN.md §6, §7).
//!
//! These definitions are part of the trusted computing base: they assert
//! that the Rust functions behave like the Lean bodies below.

/// A modeled item: Aeneas's name pattern and its Lean definition.
pub struct Model {
    pub pattern: &'static str,
    pub lean: &'static str,
}

/// The scalar types: `HashMap` keys may have them (their `Hash` instances are
/// trivial models), and the bit-counting methods are modeled for each.
const HASH_SCALARS: &[(&str, &str)] = &[
    ("u8", "U8"), ("u16", "U16"), ("u32", "U32"), ("u64", "U64"), ("u128", "U128"), ("usize", "Usize"),
    ("i8", "I8"), ("i16", "I16"), ("i32", "I32"), ("i64", "I64"), ("i128", "I128"), ("isize", "Isize"),
];

/// Definitions shared by the models live in `Vocab.lean` (`Djinn.Vocab`),
/// which the specification's views use as well. Kept here only for reference.
#[allow(dead_code)]
const PRELUDE: &str = r#"
namespace Djinn.Models

/-- The bytes of a Rust string: its UTF-8 encoding. This is the view the
    specification language gives a `String`, the same as a `&str`'s. -/
def bytes (s : String) : List U8 :=
  s.toUTF8.toList.map (fun b => U8.ofNatCore b.toNat (by have := b.toNat_lt; simp [UScalarTy.numBits]; omega))

/-- A string from bytes, when they are valid UTF-8. -/
def ofBytes (l : List U8) : Option String :=
  String.fromUTF8? ⟨(l.map (fun b => UInt8.ofNat b.val)).toArray⟩

/-- Lookup through Rust's `Borrow` and `Eq` instances: the first entry whose
    borrowed key equals the query. -/
def find {K V Q : Type} (borrow : K → Result Q) (eq : Q → Q → Result Bool) :
    List (K × V) → Q → Result (Option (K × V))
  | [], _ => ok none
  | (k, v) :: rest, q => do
    let kq ← borrow k
    let b ← eq kq q
    if b then ok (some (k, v)) else find borrow eq rest q

/-- Replace the value of the first entry whose key equals `k`. -/
def replace {K V : Type} (eq : K → K → Result Bool) : List (K × V) → K → V → Result (List (K × V))
  | [], _, _ => ok []
  | (k', v') :: rest, k, v => do
    let b ← eq k' k
    if b then ok ((k', v) :: rest) else do
      let r ← replace eq rest k v
      ok ((k', v') :: r)

/-- Drop the first entry whose borrowed key equals the query. -/
def erase {K V Q : Type} (borrow : K → Result Q) (eq : Q → Q → Result Bool) :
    List (K × V) → Q → Result (List (K × V))
  | [], _ => ok []
  | (k', v') :: rest, q => do
    let kq ← borrow k'
    let b ← eq kq q
    if b then ok rest else do
      let r ← erase borrow eq rest q
      ok ((k', v') :: r)

end Djinn.Models
"#;

/// Type models (`TypesExternal.lean`).
pub const TYPES: &[Model] = &[
    Model {
        pattern: "std::collections::hash::map::HashMap",
        lean: r#"/-- `std::collections::HashMap<K, V>`, modeled as an association list: the
    entries in insertion order, no key twice. Hashing is irrelevant to the
    model; equality of keys is Rust's `Eq` instance, passed to every operation. -/
@[rust_type "std::collections::hash::map::HashMap"]
structure std.collections.hash.map.HashMap (K : Type) (V : Type) (S : Type) (A : Type) where
  entries : List (K × V)
"#,
    },
    Model {
        pattern: "memchr::memchr::Memchr",
        lean: r#"/-- `memchr::Memchr<'h>`, the iterator over the positions of a byte in a
    haystack, modeled as the pair; its `count` is `List.count`. -/
@[rust_type "memchr::memchr::Memchr"]
structure memchr.memchr.Memchr where
  needle : Std.U8
  haystack : Aeneas.Std.Slice Std.U8
"#,
    },
    Model { pattern: "std::hash::random::RandomState", lean: "@[rust_type \"std::hash::random::RandomState\"]\ninductive std.hash.random.RandomState where | mk\n" },
    Model { pattern: "std::hash::random::DefaultHasher", lean: "@[rust_type \"std::hash::random::DefaultHasher\"]\ninductive std.hash.random.DefaultHasher where | mk\n" },
    Model { pattern: "alloc::string::FromUtf8Error", lean: "@[rust_type \"alloc::string::FromUtf8Error\"]\ninductive alloc.string.FromUtf8Error where | mk\n" },
];

/// Function models (`FunsExternal.lean`); the hashing models for the scalar
/// key types are generated (`hash_models`).
pub const FUNS: &[Model] = &[
    // ---- hashing: irrelevant to the association-list model
    Model {
        pattern: "std::hash::random::{core::hash::Hasher<std::hash::random::DefaultHasher>}::finish",
        lean: "def std.hash.random.DefaultHasher.Insts.CoreHashHasher.finish\n  : std.hash.random.DefaultHasher → Result Std.U64 := fun _ => ok 0#u64\n",
    },
    Model {
        pattern: "std::hash::random::{core::hash::Hasher<std::hash::random::DefaultHasher>}::write",
        lean: "def std.hash.random.DefaultHasher.Insts.CoreHashHasher.write\n  : std.hash.random.DefaultHasher → Slice Std.U8 → Result std.hash.random.DefaultHasher := fun h _ => ok h\n",
    },
    Model {
        pattern: "std::hash::random::{core::hash::BuildHasher<std::hash::random::RandomState, std::hash::random::DefaultHasher>}::build_hasher",
        lean: "def std.hash.random.RandomState.Insts.CoreHashBuildHasherDefaultHasher.build_hasher\n  : std.hash.random.RandomState → Result std.hash.random.DefaultHasher := fun _ => ok .mk\n",
    },
    // ---- small conversions the map API drags in
    Model {
        pattern: "core::borrow::{core::borrow::Borrow<@T, @T>}::borrow",
        lean: "def core.borrow.Borrow.Blanket.borrow {T : Type} : T → Result T := fun x => ok x\n",
    },
    Model {
        pattern: "core::option::{core::option::Option<&'0 @T>}::copied",
        lean: "def core.option.OptionShared0T.copied\n  {T : Type} (markerCopyInst : core.marker.Copy T) : Option T → Result (Option T) := fun o => ok o\n",
    },
    Model {
        pattern: "core::result::{core::result::Result<@T, @E>}::ok",
        lean: "def core.result.Result.ok\n  {T : Type} {E : Type} : core.result.Result T E → Result (Option T) :=\n  fun r => Std.Result.ok (match r with | .Ok x => some x | .Err _ => none)\n",
    },
    // ---- HashMap
    Model {
        pattern: "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, std::hash::random::RandomState, alloc::alloc::Global>}::new",
        lean: "def std.collections.hash.map.HashMapKVRandomStateGlobal.new\n  (K : Type) (V : Type) :\n  Result (std.collections.hash.map.HashMap K V std.hash.random.RandomState Global) := ok ⟨[]⟩\n",
    },
    Model {
        pattern: "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::len",
        lean: "def std.collections.hash.map.HashMap.len\n  {K : Type} {V : Type} {S : Type} {A : Type} (m : std.collections.hash.map.HashMap K V S A) : Result Std.Usize :=\n  if h : m.entries.length ≤ Usize.max then ok (Usize.ofNatCore m.entries.length (by scalar_tac)) else fail .panic\n",
    },
    Model {
        pattern: "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::is_empty",
        lean: "def std.collections.hash.map.HashMap.is_empty\n  {K : Type} {V : Type} {S : Type} {A : Type} (m : std.collections.hash.map.HashMap K V S A) : Result Bool :=\n  ok m.entries.isEmpty\n",
    },
    Model {
        pattern: "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::get",
        lean: "def std.collections.hash.map.HashMap.get\n  {K : Type} {V : Type} {S : Type} {A : Type} {Q : Type} {Clause2_Hasher : Type}\n  (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)\n  (corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher)\n  (coreborrowBorrowInst : core.borrow.Borrow K Q) (corehashHashInst1 : core.hash.Hash Q)\n  (corecmpEqInst1 : core.cmp.Eq Q) (m : std.collections.hash.map.HashMap K V S A) (q : Q) : Result (Option V) := do\n  let r ← Djinn.Vocab.find coreborrowBorrowInst.borrow corecmpEqInst1.partialEqInst.eq m.entries q\n  ok (r.map (·.2))\n",
    },
    Model {
        pattern: "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::contains_key",
        lean: "def std.collections.hash.map.HashMap.contains_key\n  {K : Type} {V : Type} {S : Type} {A : Type} {Q : Type} {Clause2_Hasher : Type}\n  (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)\n  (corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher)\n  (coreborrowBorrowInst : core.borrow.Borrow K Q) (corehashHashInst1 : core.hash.Hash Q)\n  (corecmpEqInst1 : core.cmp.Eq Q) (m : std.collections.hash.map.HashMap K V S A) (q : Q) : Result Bool := do\n  let r ← Djinn.Vocab.find coreborrowBorrowInst.borrow corecmpEqInst1.partialEqInst.eq m.entries q\n  ok r.isSome\n",
    },
    Model {
        pattern: "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::insert",
        lean: "def std.collections.hash.map.HashMap.insert\n  {K : Type} {V : Type} {S : Type} {A : Type} {Clause2_Hasher : Type}\n  (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)\n  (corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher)\n  (m : std.collections.hash.map.HashMap K V S A) (k : K) (v : V) :\n  Result ((Option V) × (std.collections.hash.map.HashMap K V S A)) := do\n  let r ← Djinn.Vocab.find (fun k' => ok k') corecmpEqInst.partialEqInst.eq m.entries k\n  match r with\n  | some (_, old) => do\n    let es ← Djinn.Vocab.replace corecmpEqInst.partialEqInst.eq m.entries k v\n    ok (some old, ⟨es⟩)\n  | none => if m.entries.length + 1 ≤ Usize.max then ok (none, ⟨m.entries ++ [(k, v)]⟩) else fail .panic\n",
    },
    Model {
        pattern: "std::collections::hash::map::{std::collections::hash::map::HashMap<@K, @V, @S, @A>}::remove",
        lean: "def std.collections.hash.map.HashMap.remove\n  {K : Type} {V : Type} {S : Type} {A : Type} {Q : Type} {Clause2_Hasher : Type}\n  (corecmpEqInst : core.cmp.Eq K) (corehashHashInst : core.hash.Hash K)\n  (corehashBuildHasherInst : core.hash.BuildHasher S Clause2_Hasher)\n  (coreborrowBorrowInst : core.borrow.Borrow K Q) (corehashHashInst1 : core.hash.Hash Q)\n  (corecmpEqInst1 : core.cmp.Eq Q) (m : std.collections.hash.map.HashMap K V S A) (q : Q) :\n  Result ((Option V) × (std.collections.hash.map.HashMap K V S A)) := do\n  let r ← Djinn.Vocab.find coreborrowBorrowInst.borrow corecmpEqInst1.partialEqInst.eq m.entries q\n  let es ← Djinn.Vocab.erase coreborrowBorrowInst.borrow corecmpEqInst1.partialEqInst.eq m.entries q\n  ok (r.map (·.2), ⟨es⟩)\n",
    },
    // ---- String, as its UTF-8 bytes
    // the `memchr` crate: SIMD byte search, modeled as the first / last index
    // (`Djinn.Vocab.memchr_eq_some`, `memchr_eq_none` and the `memrchr`
    // twins characterize them)
    Model {
        pattern: "memchr::memchr::memchr",
        lean: "def memchr.memchr.memchr (n : Std.U8) (h : Slice Std.U8) : Result (Option Std.Usize) :=\n  ok (match hm : Djinn.Vocab.memchr n h.val with\n      | none => none\n      | some i => some (Usize.ofNatCore i (by\n          have h1 := (Djinn.Vocab.memchr_eq_some.mp hm).1\n          have h2 := h.property\n          scalar_tac)))\n",
    },
    Model {
        pattern: "memchr::memchr::memrchr",
        lean: "def memchr.memchr.memrchr (n : Std.U8) (h : Slice Std.U8) : Result (Option Std.Usize) :=\n  ok (match hm : Djinn.Vocab.memrchr n h.val with\n      | none => none\n      | some i => some (Usize.ofNatCore i (by\n          have h1 := (Djinn.Vocab.memrchr_eq_some.mp hm).1\n          have h2 := h.property\n          scalar_tac)))\n",
    },
    Model {
        pattern: "memchr::memchr::memchr_iter",
        lean: "def memchr.memchr.memchr_iter (n : Std.U8) (h : Slice Std.U8) : Result memchr.memchr.Memchr := ok ⟨n, h⟩\n",
    },
    Model {
        pattern: "memchr::memchr::{core::iter::traits::iterator::Iterator<memchr::memchr::Memchr<'h>, usize>}::count",
        lean: "def memchr.memchr.Memchr.Insts.CoreIterTraitsIteratorIteratorUsize.count (it : memchr.memchr.Memchr) : Result Std.Usize :=\n  ok (Usize.ofNatCore (it.haystack.val.count it.needle) (by\n      have h1 := Djinn.Vocab.count_le_length' it.needle it.haystack.val\n      have h2 := it.haystack.property\n      scalar_tac))\n",
    },
    // ---- slices and vectors
    Model {
        pattern: "alloc::vec::{alloc::vec::Vec<@T>}::truncate",
        lean: "def alloc.vec.Vec.truncate {T : Type} (A : Type) (v : alloc.vec.Vec T) (n : Std.Usize) : Result (alloc.vec.Vec T) :=\n  ok (alloc.vec.Vec.from (v.val.take n.val) (by have := v.property; simp only [List.length_take]; omega))\n",
    },
    // `v.pop()`: the last element, if any, and the vector without it
    // (`List.getLast?`, `List.dropLast`)
    Model {
        pattern: "alloc::vec::{alloc::vec::Vec<@T>}::pop",
        lean: "def alloc.vec.Vec.pop {T : Type} (A : Type) (v : alloc.vec.Vec T) : Result ((Option T) × (alloc.vec.Vec T)) :=\n  ok (v.val.getLast?, alloc.vec.Vec.from v.val.dropLast (by have := v.property; simp only [List.length_dropLast]; omega))\n",
    },
    // `v.remove(i)`: the element at `i` and the vector without it
    // (`List.eraseIdx`); panics when `i` is out of bounds, as Rust does
    Model {
        pattern: "alloc::vec::{alloc::vec::Vec<@T>}::remove",
        lean: "def alloc.vec.Vec.remove {T : Type} (A : Type) (v : alloc.vec.Vec T) (i : Std.Usize) : Result (T × (alloc.vec.Vec T)) :=\n  if h : i.val < v.val.length then\n    ok (v.val[i.val], alloc.vec.Vec.from (v.val.eraseIdx i.val) (by have := v.property; simp only [List.length_eraseIdx, h, if_true]; omega))\n  else fail .panic\n",
    },
    // `a..b` as `RangeBounds`: what `copy_within` and other range-taking
    // methods ask of their argument
    Model {
        pattern: "core::ops::range::{core::ops::range::RangeBounds<core::ops::range::Range<@T>, @T>}::start_bound",
        lean: "def core.ops.range.Range.Insts.CoreOpsRangeRangeBounds.start_bound {T : Type} (r : core.ops.range.Range T) : Result (core.ops.range.Bound T) :=\n  ok (.Included r.start)\n",
    },
    Model {
        pattern: "core::ops::range::{core::ops::range::RangeBounds<core::ops::range::Range<@T>, @T>}::end_bound",
        lean: "def core.ops.range.Range.Insts.CoreOpsRangeRangeBounds.end_bound {T : Type} (r : core.ops.range.Range T) : Result (core.ops.range.Bound T) :=\n  ok (.Excluded r.«end»)\n",
    },
    // `s.copy_within(src, dest)`: `memmove` (the source is read before any
    // write); panics when the range is reversed or out of bounds, or the
    // destination too short, as Rust does
    Model {
        pattern: "core::slice::{[@T]}::copy_within",
        lean: "def core.slice.Slice.copy_within {T : Type} {R : Type} (inst : core.ops.range.RangeBounds R Std.Usize)\n  (copyInst : core.marker.Copy T) (s : Slice T) (src : R) (dest : Std.Usize) : Result (Slice T) := do\n  let sb ← inst.start_bound src\n  let eb ← inst.end_bound src\n  let a : Nat := match sb with | .Included x => x.val | .Excluded x => x.val + 1 | .Unbounded => 0\n  let b : Nat := match eb with | .Included x => x.val + 1 | .Excluded x => x.val | .Unbounded => s.val.length\n  (if h : a ≤ b ∧ b ≤ s.val.length ∧ dest.val + (b - a) ≤ s.val.length then\n    ok (Slice.from (s.val.take dest.val ++ (s.val.drop a).take (b - a) ++ s.val.drop (dest.val + (b - a)))\n      (by have := s.property; simp only [List.length_append, List.length_take, List.length_drop]; omega))\n  else fail .panic)\n",
    },
    // `s.sort()`: stable, with Rust's `Ord::cmp` — but only on elements the
    // order is lawful on (`cmp` never fails, reverses when swapped, "not
    // greater" is transitive, and `PartialOrd::lt`, which Rust's sort calls,
    // agrees): only then is the result of Rust's sort determined (the unique
    // stable sort); otherwise it is unspecified or a panic, and the model
    // fails. `alloc.slice.Slice.sort_ok` discharges the check for a lawful
    // `cmp`. (`sort_unstable` has no model: the order it leaves equal
    // elements in is unspecified, which no deterministic model may pin; call
    // `sort` instead)
    Model {
        pattern: "alloc::slice::{[@T]}::sort",
        lean: r#"/-- `p` holds of every element, evaluated in order (a failure fails). -/
def Djinn.Models.allM {α : Type} (p : α → Result Bool) : List α → Result Bool
  | [] => ok true
  | x :: xs => do
    let b ← p x
    if b then Djinn.Models.allM p xs else ok false

/-- The elements of `l` are ordered lawfully by `inst`: `cmp` never fails on
    them, swapping the arguments reverses it, "not greater" is transitive (a
    total preorder), and `PartialOrd::lt` — what Rust's sort calls — is "less". -/
def Djinn.Models.lawfulOn {T : Type} (inst : core.cmp.Ord T) (l : List T) : Result Bool :=
  Djinn.Models.allM (fun a => Djinn.Models.allM (fun b => do
    let ab ← inst.cmp a b
    let ba ← inst.cmp b a
    let lt ← inst.partialOrdInst.lt a b
    let tr ← Djinn.Models.allM (fun c => do
      let bc ← inst.cmp b c
      let ac ← inst.cmp a c
      ok (ab == .gt || bc == .gt || ac != .gt)) l
    ok (ba == ab.swap && lt == (ab == .lt) && tr)) l) l

/-- The stable insertion sort with `cmp`: what `s.sort()` returns when the
    order is lawful on the elements (`Djinn.Vocab.sortM_ok`). -/
def Djinn.Models.sortStable {T : Type} (ordInst : core.cmp.Ord T) (s : Slice T) : Result (Slice T) := do
  let l ← Djinn.Vocab.sortM ordInst.cmp s.val
  (if h : l.length ≤ Usize.max then ok (Slice.from l h) else fail .panic)

def alloc.slice.Slice.sort {T : Type} (ordInst : core.cmp.Ord T) (s : Slice T) : Result (Slice T) := do
  let lawful ← Djinn.Models.lawfulOn ordInst s.val
  if lawful then Djinn.Models.sortStable ordInst s else fail .panic

theorem Djinn.Models.allM_true {α : Type} (p : α → Result Bool) (l : List α) (h : ∀ x ∈ l, p x = ok true) :
    Djinn.Models.allM p l = ok true := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp [Djinn.Models.allM, h x (by simp), ih (fun y hy => h y (by simp [hy]))]

/-- With a lawful order (`f`: `cmp`'s values), the check passes. -/
theorem Djinn.Models.lawfulOn_ok {T : Type} (inst : core.cmp.Ord T) (f : T → T → Ordering)
    (hcmp : ∀ a b, inst.cmp a b = ok (f a b)) (hlt : ∀ a b, inst.partialOrdInst.lt a b = ok (f a b == .lt))
    (hswap : ∀ a b, f b a = (f a b).swap) (htrans : ∀ a b c, f a b ≠ .gt → f b c ≠ .gt → f a c ≠ .gt)
    (l : List T) : Djinn.Models.lawfulOn inst l = ok true := by
  unfold Djinn.Models.lawfulOn
  apply Djinn.Models.allM_true; intro a _
  apply Djinn.Models.allM_true; intro b _
  have htr : Djinn.Models.allM (fun c => ok (f a b == .gt || f b c == .gt || f a c != .gt)) l = ok true := by
    apply Djinn.Models.allM_true; intro c _
    have := htrans a b c
    clear hswap hlt hcmp htrans
    cases hab : f a b <;> cases hbc : f b c <;> cases hac : f a c <;> simp_all
  simp only [hcmp, hlt]
  rw [hswap a b]
  clear hswap htrans hcmp hlt
  cases hab : f a b <;> simp_all

/-- `s.sort()` with a lawful order: the stable insertion sort of the model. -/
theorem alloc.slice.Slice.sort_ok {T : Type} (inst : core.cmp.Ord T) (f : T → T → Ordering)
    (hcmp : ∀ a b, inst.cmp a b = ok (f a b)) (hlt : ∀ a b, inst.partialOrdInst.lt a b = ok (f a b == .lt))
    (hswap : ∀ a b, f b a = (f a b).swap) (htrans : ∀ a b c, f a b ≠ .gt → f b c ≠ .gt → f a c ≠ .gt)
    (s : Slice T) :
    alloc.slice.Slice.sort inst s = Djinn.Models.sortStable inst s := by
  simp [alloc.slice.Slice.sort, Djinn.Models.lawfulOn_ok inst f hcmp hlt hswap htrans]
"#,
    },
    // `str` is `Slice U8` in Aeneas: its bytes are itself
    Model { pattern: "core::str::{str}::as_bytes", lean: "def core.str.Str.as_bytes (s : Str) : Result (Slice Std.U8) := ok s\n" },
    Model { pattern: "alloc::string::{alloc::string::String}::new", lean: "def alloc.string.String.new : Result String := ok \"\"\n" },
    Model {
        pattern: "alloc::string::{alloc::string::String}::len",
        lean: "def alloc.string.String.len (s : String) : Result Std.Usize :=\n  if h : s.utf8ByteSize ≤ Usize.max then ok (Usize.ofNatCore s.utf8ByteSize (by scalar_tac)) else fail .panic\n",
    },
    Model { pattern: "alloc::string::{alloc::string::String}::is_empty", lean: "def alloc.string.String.is_empty (s : String) : Result Bool := ok s.isEmpty\n" },
    Model { pattern: "alloc::string::{alloc::string::String}::push", lean: "def alloc.string.String.push (s : String) (c : Char) : Result String := ok (s.push c)\n" },
    Model {
        pattern: "alloc::string::{alloc::string::String}::push_str",
        lean: "def alloc.string.String.push_str (s : String) (t : Str) : Result String :=\n  match Djinn.Vocab.ofBytes t.val with\n  | some u => ok (s ++ u)\n  | none => fail .panic\n",
    },
    Model {
        pattern: "alloc::string::{alloc::string::String}::as_bytes",
        lean: "def alloc.string.String.as_bytes (s : String) : Result (Slice Std.U8) :=\n  if h : (Djinn.Vocab.bytes s).length ≤ Usize.max then ok (Slice.from (Djinn.Vocab.bytes s) h) else fail .panic\n",
    },
    Model {
        pattern: "alloc::string::{alloc::string::String}::as_str",
        lean: "def alloc.string.String.as_str (s : String) : Result Str :=\n  if h : (Djinn.Vocab.bytes s).length ≤ Usize.max then ok (Slice.from (Djinn.Vocab.bytes s) h) else fail .panic\n",
    },
    Model {
        pattern: "alloc::string::{alloc::string::String}::into_bytes",
        lean: "def alloc.string.String.into_bytes (s : String) : Result (alloc.vec.Vec Std.U8) :=\n  if h : (Djinn.Vocab.bytes s).length ≤ Usize.max then ok (alloc.vec.Vec.from (Djinn.Vocab.bytes s) h) else fail .panic\n",
    },
    Model {
        pattern: "alloc::string::{alloc::string::String}::from_utf8",
        lean: "def alloc.string.String.from_utf8\n  (v : alloc.vec.Vec Std.U8) : Result (core.result.Result String alloc.string.FromUtf8Error) :=\n  ok (match Djinn.Vocab.ofBytes v.val with | some s => .Ok s | none => .Err .mk)\n",
    },
    Model { pattern: "alloc::string::{core::clone::Clone<alloc::string::String>}::clone", lean: "def alloc.string.String.Insts.CoreCloneClone.clone (s : String) : Result String := ok s\n" },
    Model {
        pattern: "alloc::string::{core::cmp::PartialEq<alloc::string::String, alloc::string::String>}::eq",
        lean: "def alloc.string.String.Insts.CoreCmpPartialEqString.eq (s t : String) : Result Bool := ok (s == t)\n",
    },
    Model {
        pattern: "alloc::string::{core::convert::From<alloc::string::String, &'0 str>}::from",
        lean: "def alloc.string.String.Insts.CoreConvertFromShared0Str.from (t : Str) : Result String :=\n  match Djinn.Vocab.ofBytes t.val with\n  | some u => ok u\n  | none => fail .panic\n",
    },
];

/// The hashing models for the scalar key types.
fn hash_models() -> Vec<(String, String)> {
    HASH_SCALARS
        .iter()
        .map(|(rust, lean)| {
            (
                format!("core::hash::impls::{{core::hash::Hash<{rust}>}}::hash"),
                format!("def {lean}.Insts.CoreHashHash.hash\n  {{H : Type}} (HasherInst : core.hash.Hasher H) : Std.{lean} → H → Result H := fun _ h => ok h\n"),
            )
        })
        .collect()
}

/// The bit-counting methods Aeneas has no model of, for every integer type
/// (Aeneas models `leading_zeros` itself). Each is Lean core's `BitVec`
/// operation on the value's bits: `cpop` (population count), `ctz`, `clz`,
/// on the bits or their complement, as a `u32` like Rust's result. All are
/// total: `x.trailing_zeros()` of 0 is the width, as `BitVec.ctz 0` is.
fn bit_count_models() -> Vec<(String, String)> {
    const METHODS: &[(&str, &str)] = &[
        ("count_ones", "x.bv.cpop"),
        ("count_zeros", "(~~~x.bv).cpop"),
        ("trailing_zeros", "x.bv.ctz"),
        ("trailing_ones", "(~~~x.bv).ctz"),
        ("leading_ones", "(~~~x.bv).clz"),
    ];
    HASH_SCALARS
        .iter()
        .flat_map(|(rust, lean)| {
            METHODS.iter().map(move |(m, bits)| {
                (
                    format!("core::num::{{{rust}}}::{m}"),
                    format!("def core.num.{lean}.{m} (x : Std.{lean}) : Result Std.U32 :=\n  ok ⟨BitVec.ofNat 32 ({bits}).toNat⟩\n"),
                )
            })
        })
        .collect()
}

/// The Lean definition for a pattern, if the library has one.
pub fn lookup(pattern: &str) -> Option<String> {
    if let Some(m) = TYPES.iter().chain(FUNS.iter()).find(|m| m.pattern == pattern) {
        return Some(m.lean.to_string());
    }
    hash_models().into_iter().chain(bit_count_models()).find(|(p, _)| p == pattern).map(|(_, l)| l)
}

fn is_type(pattern: &str) -> bool {
    TYPES.iter().any(|m| m.pattern == pattern)
}

/// Cover the externals Aeneas listed: `Ok((FunsExternal.lean, TypesExternal.lean))`
/// when every pattern has a model, else the uncovered patterns. `tables` are
/// the models of the specification's tables (pattern, Lean), defined from
/// `Tables.lean`.
pub fn cover(ns: &str, patterns: &[String], tables: &[(String, String)]) -> Result<(String, String), Vec<String>> {
    let table = |p: &str| tables.iter().find(|(q, _)| q == p).map(|(_, l)| l.clone());
    let lookup = |p: &str| lookup(p).or_else(|| table(p));
    let uncovered: Vec<String> = patterns.iter().filter(|p| lookup(p).is_none()).cloned().collect();
    if !uncovered.is_empty() {
        return Err(uncovered);
    }
    let header = |imports: &str| {
        format!(
            "-- Written by `cargo djinn` from its model library (DESIGN.md §6): trusted Lean models\n-- of standard-library items Aeneas has no model for. Regenerated on every verify.\nmodule\npublic import Aeneas\n{imports}@[expose] public section\nopen Aeneas Aeneas.Std Result ControlFlow Error\nset_option linter.dupNamespace false\nset_option linter.hashCommand false\nset_option linter.unusedVariables false\nset_option linter.style.whitespace false\nset_option linter.style.setOption false\nset_option linter.style.longLine false\nset_option maxHeartbeats 1000000\n\n"
        )
    };
    let mut types = header("");
    for p in patterns.iter().filter(|p| is_type(p)) {
        types.push_str(&lookup(p).unwrap());
        types.push('\n');
    }
    let uses_tables = patterns.iter().any(|p| table(p).is_some());
    let tables_import = if uses_tables { format!("public import {ns}.Tables\n") } else { String::new() };
    let mut funs = header(&format!("public import {ns}.Code.Types\npublic import {ns}.Vocab\n{tables_import}"));
    funs.push_str(&format!("open {ns}\n\n"));
    for p in patterns.iter().filter(|p| !is_type(p)) {
        funs.push_str(&lookup(p).unwrap());
        funs.push('\n');
    }
    Ok((funs, types))
}

#[cfg(test)]
mod tests {
    use super::lookup;

    #[test]
    fn bit_counting_models_cover_every_integer_type() {
        for t in ["u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64", "i128", "isize"] {
            for m in ["count_ones", "count_zeros", "trailing_zeros", "trailing_ones", "leading_ones"] {
                assert!(lookup(&format!("core::num::{{{t}}}::{m}")).is_some(), "{t}::{m}");
            }
        }
        assert_eq!(
            lookup("core::num::{u64}::trailing_zeros").unwrap(),
            "def core.num.U64.trailing_zeros (x : Std.U64) : Result Std.U32 :=\n  ok ⟨BitVec.ofNat 32 (x.bv.ctz).toNat⟩\n"
        );
        // Aeneas models `leading_zeros` itself
        assert!(lookup("core::num::{u64}::leading_zeros").is_none());
    }

    #[test]
    fn slice_and_vec_models() {
        for p in [
            "alloc::vec::{alloc::vec::Vec<@T>}::truncate",
            "alloc::vec::{alloc::vec::Vec<@T>}::pop",
            "alloc::vec::{alloc::vec::Vec<@T>}::remove",
            "core::slice::{[@T]}::copy_within",
            "alloc::slice::{[@T]}::sort",
            "core::ops::range::{core::ops::range::RangeBounds<core::ops::range::Range<@T>, @T>}::start_bound",
            "core::ops::range::{core::ops::range::RangeBounds<core::ops::range::Range<@T>, @T>}::end_bound",
        ] {
            assert!(lookup(p).is_some(), "{p}");
        }
        // no deterministic model may pin the order of equal elements
        assert!(lookup("core::slice::{[@T]}::sort_unstable").is_none());
        // `sort`'s result is pinned only for an order lawful on the elements
        // (else Rust's is unspecified): the model checks it, and fails without
        let sort = lookup("alloc::slice::{[@T]}::sort").unwrap();
        assert!(sort.contains("let lawful ← Djinn.Models.lawfulOn ordInst s.val"));
        assert!(sort.contains("if lawful then Djinn.Models.sortStable ordInst s else fail .panic"));
        assert!(sort.contains("theorem alloc.slice.Slice.sort_ok"));
    }

    #[test]
    fn tables_are_covered_from_their_models() {
        let tables = vec![("bits::spec::K".to_string(), "def spec.K : Result (Slice Std.U32) := sorry\n".to_string())];
        let pats = vec!["bits::spec::K".to_string(), "core::num::{u64}::count_ones".to_string()];
        let (funs, _) = super::cover("Bits", &pats, &tables).unwrap();
        assert!(funs.contains("public import Bits.Tables"));
        assert!(funs.contains("def spec.K"));
        assert!(super::cover("Bits", &["bits::spec::Other".to_string()], &tables).is_err());
        // without tables, no import of the tables module
        let (funs, _) = super::cover("Bits", &pats[1..], &[]).unwrap();
        assert!(!funs.contains("Bits.Tables"));
    }
}
