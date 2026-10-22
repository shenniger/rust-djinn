import Gzip.Proofs.Decode.RoundTrip

open Aeneas Std
open Gzip.Spec Gzip.Proofs.Decode.Decoding Gzip.Proofs.Decode.Huffman Gzip.Proofs.Decode.Parsing Gzip.Proofs.Decode.RoundTrip

namespace Gzip.Proofs.Decode.Encoding

def lengthBases : List ℤ := [3,4,5,6,7,8,9,10,11,13,15,17,19,23,27,31,35,43,51,59,67,83,99,115,131,163,195,227,258]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem lbase_values (k b : ℤ) (h : lbase_spec k b) : b = lengthBases[k.toNat]! := by
  generalize hm : k.toNat = m
  induction m using Nat.strong_induction_on generalizing k b with
  | h m ih =>
    rw [← hm]
    rw [lbase_spec] at h
    have hk0 := h.1
    change 0 ≤ k at hk0
    obtain ⟨hk28, hb⟩ := h.2 hk0
    replace hb := hb hk28
    by_cases hz : k = 0
    · subst k; simpa [lengthBases] using hb.1 rfl
    by_cases ht : k = 28
    · subst k; simpa [lengthBases] using (hb.2 (by omega)).1 rfl
    obtain ⟨a, ha, e, he, hbe⟩ := (hb.2 hz).2 ht
    have hav := ih (k - 1).toNat (hm ▸ int_step_decreases k hk0 hz) (k - 1) a ha rfl
    have hk1 : 1 ≤ k := by omega
    have hk27 : k ≤ 27 := by omega
    clear h hb ha ih hm hk0 hk28 hz ht
    interval_cases k <;> norm_num [lextra_spec, lextra_pre, lengthBases, Int.toNat] at he hav ⊢ <;> subst e <;> norm_num [Int.toNat] at hbe <;> omega

def distanceBases : List ℤ := [1,2,3,4,5,7,9,13,17,25,33,49,65,97,129,193,257,385,513,769,1025,1537,2049,3073,4097,6145,8193,12289,16385,24577]

theorem dbase_values (k b : ℤ) (h : dbase_spec k b) : b = distanceBases[k.toNat]! := by
  generalize hm : k.toNat = m
  induction m using Nat.strong_induction_on generalizing k b with
  | h m ih =>
    rw [← hm]
    rw [dbase_spec] at h
    have hk0 := h.1
    change 0 ≤ k at hk0
    obtain ⟨hk29, hb⟩ := h.2 hk0
    replace hb := hb hk29
    by_cases hz : k = 0
    · subst k; simpa [distanceBases] using hb.1 rfl
    obtain ⟨a, ha, e, he, hbe⟩ := hb.2 hz
    have hav := ih (k - 1).toNat (hm ▸ int_step_decreases k hk0 hz) (k - 1) a ha rfl
    have hk1 : 1 ≤ k := by omega
    clear h hb ha ih hm hk0 hz
    interval_cases k <;> norm_num [dextra_spec, dextra_pre, distanceBases, Int.toNat] at he hav ⊢ <;> subst e <;> norm_num [Int.toNat] at hbe <;> omega

theorem lengthBases_mono : ∀ a b : Fin 29, a.val ≤ b.val → lengthBases[a.val]! ≤ lengthBases[b.val]! := by decide

set_option maxRecDepth 4096 in
theorem distanceBases_mono : ∀ a b : Fin 30, a.val ≤ b.val → distanceBases[a.val]! ≤ distanceBases[b.val]! := by decide

theorem lbase_mono (a b x y : ℤ) (hab : a ≤ b)
    (hx : lbase_spec a x) (hy : lbase_spec b y) : x ≤ y := by
  have hxv := lbase_values a x hx
  have hyv := lbase_values b y hy
  rw [lbase_spec] at hx hy
  have ha := (hx.2 hx.1).1
  have hb := (hy.2 hy.1).1
  have ha0 : 0 ≤ a := hx.1
  have hb0 : 0 ≤ b := hy.1
  rw [hxv, hyv]
  exact lengthBases_mono ⟨a.toNat, by omega⟩ ⟨b.toNat, by omega⟩ (by change a.toNat ≤ b.toNat; omega)

theorem dbase_mono (a b x y : ℤ) (hab : a ≤ b)
    (hx : dbase_spec a x) (hy : dbase_spec b y) : x ≤ y := by
  have hxv := dbase_values a x hx
  have hyv := dbase_values b y hy
  rw [dbase_spec] at hx hy
  have ha := (hx.2 hx.1).1
  have hb := (hy.2 hy.1).1
  have ha0 : 0 ≤ a := hx.1
  have hb0 : 0 ≤ b := hy.1
  rw [hxv, hyv]
  exact distanceBases_mono ⟨a.toNat, by omega⟩ ⟨b.toNat, by omega⟩ (by change a.toNat ≤ b.toNat; omega)

def rawBit (s : List U8) (i : ℤ) : ℤ := (s[(i / 8).toNat]!).val / 2 ^ (i % 8).toNat % 2

def BitsEq (s t : List U8) (lo hi : ℤ) : Prop :=
  ∀ q : ℤ, lo ≤ q → q < hi → rawBit s q = rawBit t q

theorem bit_raw (s : List U8) (i v : ℤ) (h : bit_spec s i v) : rawBit s i = v := h.2.2.symm

theorem bit_range (s : List U8) (i v : ℤ) (h : bit_spec s i v) : 0 ≤ v ∧ v ≤ 1 := by
  have := h.2.2
  omega

theorem field_bits (s t : List U8) (i n v : ℤ)
    (hs : field_spec s i n v) (ht : field_spec t i n v) : BitsEq s t i (i + n) := by
  generalize hm : n.toNat = m
  induction m using Nat.strong_induction_on generalizing i n v with
  | h m ih =>
    rw [field_spec] at hs ht
    have hp := hs.1
    by_cases hn : n = 0
    · intro q hq hq'; omega
    obtain ⟨b, hb, hs'⟩ := (hs.2 hp).2 hn
    obtain ⟨b', hb', ht'⟩ := (ht.2 hp).2 hn
    obtain ⟨w, hw, he⟩ := hs' hb
    obtain ⟨w', hw', he'⟩ := ht' hb'
    have hbb := bit_range s i b hb
    have hbb' := bit_range t i b' hb'
    have hbe : b = b' := by omega
    have hwe : w = w' := by omega
    subst b'; subst w'
    have hrec := ih (n - 1).toNat (hm ▸ int_step_decreases n hp hn) (i + 1) (n - 1) w hw hw' rfl
    intro q hq hq'
    by_cases hqi : q = i
    · subst q; exact (bit_raw s i b hb).trans (bit_raw t i b hb').symm
    · exact hrec q (by omega) (by omega)

theorem code_bits (s t : List U8) (i n v : ℤ)
    (hs : code_spec s i n v) (ht : code_spec t i n v) : BitsEq s t i (i + n) := by
  generalize hm : n.toNat = m
  induction m using Nat.strong_induction_on generalizing n v with
  | h m ih =>
    rw [code_spec] at hs ht
    have hp := hs.1
    by_cases hn : n = 0
    · intro q hq hq'; omega
    obtain ⟨w, hw, b, hb, he⟩ := (hs.2 hp).2 hn
    obtain ⟨w', hw', b', hb', he'⟩ := (ht.2 hp).2 hn
    have hbb := bit_range s (i + n - 1) b hb
    have hbb' := bit_range t (i + n - 1) b' hb'
    have hbe : b = b' := by omega
    have hwe : w = w' := by omega
    subst b'; subst w'
    have hrec := ih (n - 1).toNat (hm ▸ int_step_decreases n hp hn) (n - 1) w hw hw' rfl
    intro q hq hq'
    by_cases hqi : q = i + n - 1
    · subst q; exact (bit_raw s _ b hb).trans (bit_raw t _ b hb').symm
    · exact hrec q hq (by omega)

theorem codeword_unique (lit : List U8) (sym a b : ℤ)
    (ha : codeword_spec lit sym a) (hb : codeword_spec lit sym b) : a = b := by
  obtain ⟨_, _, u, hu, v, hv, he⟩ := ha
  obtain ⟨_, _, u', hu', v', hv', he'⟩ := hb
  have := shorter_unique _ _ _ _ _ hu hu'
  have := earlier_unique _ _ _ _ _ hv hv'
  omega

theorem symbol_bits (s t lit : List U8) (i sym : ℤ)
    (hs : symbol_spec s i lit sym) (ht : symbol_spec t i lit sym) :
    BitsEq s t i (i + (lit[sym.toNat]!).val) := by
  obtain ⟨_, _, _, a, ha, hc⟩ := hs
  obtain ⟨_, _, _, b, hb, hc'⟩ := ht
  have he := codeword_unique lit sym a b ha hb
  subst b
  exact code_bits s t i _ a hc hc'

theorem BitsEq.join (s t : List U8) (a b c : ℤ) (hab : BitsEq s t a b) (hbc : BitsEq s t b c) : BitsEq s t a c := by
  intro q hq hq'
  by_cases hqb : q < b
  · exact hab q hq hqb
  · exact hbc q (by omega) hq'

theorem byte_of_bits (a b : U8)
    (h : ∀ n : Fin 8, (a.val : ℤ) / 2 ^ n.val % 2 = (b.val : ℤ) / 2 ^ n.val % 2) : a = b := by
  have h0 := h ⟨0, by decide⟩
  have h1 := h ⟨1, by decide⟩
  have h2 := h ⟨2, by decide⟩
  have h3 := h ⟨3, by decide⟩
  have h4 := h ⟨4, by decide⟩
  have h5 := h ⟨5, by decide⟩
  have h6 := h ⟨6, by decide⟩
  have h7 := h ⟨7, by decide⟩
  norm_num at h0 h1 h2 h3 h4 h5 h6 h7
  have ha := byte_bound a
  have hb := byte_bound b
  apply UScalar.eq_of_val_eq
  omega

theorem byte_of_rawBits (s t : List U8) (k : Nat)
    (h : BitsEq s t (8 * k) (8 * k + 8)) : s[k]! = t[k]! := by
  apply byte_of_bits
  intro n
  have hn := n.isLt
  have he := h (8 * k + n.val) (by omega) (by omega)
  have hdiv : (8 * (k : ℤ) + n.val) / 8 = k := by omega
  have hmod : (8 * (k : ℤ) + n.val) % 8 = n.val := by omega
  simpa only [rawBit, hdiv, hmod, Int.toNat_natCast] using he

theorem u32_bytes (s t : List U8) (i v : ℤ)
    (hs : u32le_spec s i v) (ht : u32le_spec t i v) :
    ∀ q : ℤ, i ≤ q → q < i + 4 → s[q.toNat]! = t[q.toNat]! := by
  obtain ⟨_, a, ha, b, hb, he⟩ := hs
  obtain ⟨_, a', ha', b', hb', he'⟩ := ht
  have ha0 := ha.2.2
  have hb0 := hb.2.2
  have ha0' := ha'.2.2
  have hb0' := hb'.2.2
  have h0 := byte_bound s[i.toNat]!
  have h1 := byte_bound s[(i + 1).toNat]!
  have h2 := byte_bound s[(i + 2).toNat]!
  have h3 := byte_bound s[(i + 2 + 1).toNat]!
  have h0' := byte_bound t[i.toNat]!
  have h1' := byte_bound t[(i + 1).toNat]!
  have h2' := byte_bound t[(i + 2).toNat]!
  have h3' := byte_bound t[(i + 2 + 1).toNat]!
  intro q hq hq'
  have hc : q = i ∨ q = i + 1 ∨ q = i + 2 ∨ q = i + 2 + 1 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;> apply UScalar.eq_of_val_eq <;> omega

end Gzip.Proofs.Decode.Encoding
