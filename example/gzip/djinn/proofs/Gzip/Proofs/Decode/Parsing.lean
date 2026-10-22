import Gzip.Proofs.Decode.Huffman
import Mathlib.Tactic.IntervalCases

open Aeneas Std
open Gzip.Spec Gzip.Proofs.Decode.Decoding Gzip.Proofs.Decode.Huffman

namespace Gzip.Proofs.Decode.Parsing

theorem guard_and (p q : Prop) : (p ∧ (p → q)) ↔ p ∧ q := by tauto

theorem u16_unique (s : List U8) (i x y : ℤ)
    (hx : u16le_spec s i x) (hy : u16le_spec s i y) : x = y := hx.2.2.trans hy.2.2.symm

theorem lextra_unique (k x y : ℤ) (hx : lextra_spec k x) (hy : lextra_spec k y) : x = y := by
  by_cases h : k < 8 ∨ k = 28
  · exact (hx.2.2.1 h).trans (hy.2.2.1 h).symm
  · exact (hx.2.2.2 h).trans (hy.2.2.2 h).symm

theorem dextra_unique (k x y : ℤ) (hx : dextra_spec k x) (hy : dextra_spec k y) : x = y := by
  by_cases h : k < 4
  · exact (hx.2.2.1 h).trans (hy.2.2.1 h).symm
  · exact (hx.2.2.2 h).trans (hy.2.2.2 h).symm

theorem lbase_unique (k x y : ℤ) (hx : lbase_spec k x) (hy : lbase_spec k y) : x = y := by
  generalize hm : k.toNat = m
  induction m using Nat.strong_induction_on generalizing k x y with
  | h m ih =>
    rw [lbase_spec] at hx hy
    have hp := hx.1
    have hxb := (hx.2 hp).2 (hx.2 hp).1
    have hyb := (hy.2 hp).2 (hy.2 hp).1
    by_cases hz : k = 0
    · exact (hxb.1 hz).trans (hyb.1 hz).symm
    by_cases ht : k = 28
    · exact ((hxb.2 hz).1 ht).trans ((hyb.2 hz).1 ht).symm
    obtain ⟨a, ha, e, he, hx⟩ := (hxb.2 hz).2 ht
    obtain ⟨b, hb, f, hf, hy⟩ := (hyb.2 hz).2 ht
    have hlt : (k - 1).toNat < m := hm ▸ int_step_decreases k hp hz
    have hab := ih (k - 1).toNat hlt _ _ _ ha hb rfl
    have hef := lextra_unique (k - 1) e f he hf
    grind

theorem dbase_unique (k x y : ℤ) (hx : dbase_spec k x) (hy : dbase_spec k y) : x = y := by
  generalize hm : k.toNat = m
  induction m using Nat.strong_induction_on generalizing k x y with
  | h m ih =>
    rw [dbase_spec] at hx hy
    have hp := hx.1
    have hxb := (hx.2 hp).2 (hx.2 hp).1
    have hyb := (hy.2 hp).2 (hy.2 hp).1
    by_cases hz : k = 0
    · exact (hxb.1 hz).trans (hyb.1 hz).symm
    obtain ⟨a, ha, e, he, hx⟩ := hxb.2 hz
    obtain ⟨b, hb, f, hf, hy⟩ := hyb.2 hz
    have hlt : (k - 1).toNat < m := hm ▸ int_step_decreases k hp hz
    have hab := ih (k - 1).toNat hlt _ _ _ ha hb rfl
    have hef := dextra_unique (k - 1) e f he hf
    grind

theorem list_eq (x y : List U8) (hlen : x.length = y.length)
    (h : ∀ k, k < x.length → x[k]! = y[k]!) : x = y := by
  apply List.ext_getElem hlen
  intro k hk hk'
  simpa only [getElem!_pos x k hk, getElem!_pos y k hk'] using h k hk

theorem take_eq_get (x y : List U8) (n k : Nat) (h : x.take n = y.take n)
    (hk : k < n) : x[k]! = y[k]! := by
  have he := congrArg (fun l : List U8 => l[k]!) h
  simpa [getElem!_def, List.getElem?_take, hk] using he

theorem append_unique (prev : List U8) (v : ℤ) (x y : List U8)
    (hx : append_spec prev v x) (hy : append_spec prev v y) : x = y := by
  obtain ⟨_, hxlen, hxt, hxv⟩ := hx
  obtain ⟨_, hylen, hyt, hyv⟩ := hy
  simp only [List.drop_zero, Int.toNat_natCast] at hxt hyt hxv hyv
  apply list_eq x y (by omega)
  intro k hk
  by_cases hkp : k < prev.length
  · exact take_eq_get x y prev.length k (hxt.trans hyt.symm) hkp
  · have he : k = prev.length := by omega
    subst k
    apply UScalar.eq_of_val_eq
    omega

theorem copy_unique (prev : List U8) (d len : ℤ) (x y : List U8)
    (hx : copy_spec prev d len x) (hy : copy_spec prev d len y) : x = y := by
  obtain ⟨_, hd, hxlen, hxt, hxv⟩ := hx
  obtain ⟨_, _, hylen, hyt, hyv⟩ := hy
  simp only [List.drop_zero, Int.toNat_natCast] at hxt hyt
  apply list_eq x y (by omega)
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro hk
    by_cases hkp : k < prev.length
    · exact take_eq_get x y prev.length k (hxt.trans hyt.symm) hkp
    · have he := hxv k (by omega) (by omega)
      have hf := hyv k (by omega) (by omega)
      simp only [Int.toNat_natCast] at he hf
      rw [he, hf]
      exact ih _ (by omega) (by omega)

theorem fixedlit_unique (x y : List U8) (hx : fixedlit_spec x) (hy : fixedlit_spec y) : x = y := by
  apply list_eq x y (by have := hx.2.1; have := hy.2.1; omega)
  intro k hk
  obtain ⟨a, ha, he⟩ := hx.2.2 k (by omega) (by have := hx.2.1; omega)
  obtain ⟨b, hb, hf⟩ := hy.2.2 k (by omega) (by have := hx.2.1; omega)
  apply UScalar.eq_of_val_eq
  have hab := ha.2.trans hb.2.symm
  simp only [Int.toNat_natCast] at he hf
  omega

theorem fixeddist_unique (x y : List U8) (hx : fixeddist_spec x) (hy : fixeddist_spec y) : x = y := by
  apply list_eq x y (by have := hx.2.1; have := hy.2.1; omega)
  intro k hk
  have hk' : k < y.length := by have := hx.2.1; have := hy.2.1; omega
  have he := hx.2.2 x[k]! (by simpa only [getElem!_pos x k hk] using List.getElem_mem hk)
  have hf := hy.2.2 y[k]! (by simpa only [getElem!_pos y k hk'] using List.getElem_mem hk')
  apply UScalar.eq_of_val_eq
  omega

theorem bit_measure_decreases (s : List U8) (i a : ℤ)
    (ha : i < a) (hb : a ≤ 8 * (s.length : ℤ)) :
    (8 * (s.length : ℤ) - a).toNat < (8 * (s.length : ℤ) - i).toNat := by omega

theorem symbols_unique (s lit dist prev x y : List U8) (i j k : ℤ)
    (hx : symbols_spec s i lit dist prev x j) (hy : symbols_spec s i lit dist prev y k) :
    x = y ∧ j = k := by
  generalize hm : (8 * (s.length : ℤ) - i).toNat = m
  induction m using Nat.strong_induction_on generalizing i prev x y j k with
  | h m ih =>
    rw [symbols_spec] at hx hy
    simp only [symbols_pre, true_and, forall_true_left, guard_and] at hx hy
    obtain ⟨sym, a, hs, ha, hab, hxb⟩ := hx
    obtain ⟨sym', a', hs', ha', hab', hyb⟩ := hy
    have he := symbol_unique s lit i sym sym' hs hs'
    subst sym'
    rw [← ha] at ha'
    subst a'
    by_cases hend : sym = 256
    · obtain ⟨rfl, rfl⟩ := hxb.1 hend
      obtain ⟨rfl, rfl⟩ := hyb.1 hend
      exact ⟨rfl, rfl⟩
    by_cases hlit : sym < 256
    · obtain ⟨p, hp, hx⟩ := (hxb.2 hend).1 hlit
      obtain ⟨q, hq, hy⟩ := (hyb.2 hend).1 hlit
      have he := append_unique prev sym p q hp hq
      subst q
      exact ih _ (hm ▸ bit_measure_decreases s i a hab.1 hab.2) _ _ _ _ _ _ hx hy rfl
    · obtain ⟨len, b, dc, d, c, hlen, hb, hdc, hd, hc, hcb, p, hp, hx⟩ := (hxb.2 hend).2 hlit
      obtain ⟨len', b', dc', d', c', hlen', hb', hdc', hd', hc', hcb', q, hq, hy⟩ := (hyb.2 hend).2 hlit
      have he : len = len' := by
        obtain ⟨v, hv, e, he, f, hf, h⟩ := hlen
        obtain ⟨v', hv', e', he', f', hf', h'⟩ := hlen'
        have := lbase_unique _ _ _ hv hv'
        have heq := lextra_unique _ _ _ he he'
        subst e'
        have := field_unique _ _ _ _ _ hf hf'
        omega
      subst len'
      have he : b = b' := by
        obtain ⟨e, he, h⟩ := hb
        obtain ⟨e', he', h'⟩ := hb'
        have := lextra_unique _ _ _ he he'
        omega
      subst b'
      have he := symbol_unique s dist b dc dc' hdc hdc'
      subst dc'
      have he : d = d' := by
        obtain ⟨v, hv, e, he, f, hf, h⟩ := hd
        obtain ⟨v', hv', e', he', f', hf', h'⟩ := hd'
        have := dbase_unique _ _ _ hv hv'
        have heq := dextra_unique _ _ _ he he'
        subst e'
        have := field_unique _ _ _ _ _ hf hf'
        omega
      subst d'
      have he : c = c' := by
        obtain ⟨e, he, h⟩ := hc
        obtain ⟨e', he', h'⟩ := hc'
        have := dextra_unique _ _ _ he he'
        omega
      subst c'
      have he := copy_unique prev d len p q hp hq
      subst q
      exact ih _ (hm ▸ bit_measure_decreases s i c (_root_.lt_trans hab.1 hcb.1) hcb.2) _ _ _ _ _ _ hx hy rfl

theorem stored_unique (s prev x y : List U8) (i j k : ℤ)
    (hx : stored_spec s i prev x j) (hy : stored_spec s i prev y k) :
    x = y ∧ j = k := by
  obtain ⟨_, a, len, rfl, hlen, _, _, hxlen, hxt, hxd, rfl⟩ := hx
  obtain ⟨_, a', len', ha', hlen', _, _, hylen, hyt, hyd, hk⟩ := hy
  subst a'
  have he := u16_unique _ _ _ _ hlen hlen'
  subst len'
  have hxylen : x.length = y.length := by omega
  constructor
  · simp only [List.drop_zero, Int.toNat_natCast] at hxt hyt hxd hyd
    have he : (x.length : ℤ) - prev.length = (x.length - prev.length : Nat) := by
      have hp := congrArg List.length hxt
      simp only [List.length_take] at hp
      omega
    have he' : (y.length : ℤ) - prev.length = (y.length - prev.length : Nat) := by omega
    rw [he, Int.toNat_natCast, ← List.length_drop, List.take_length] at hxd
    rw [he', Int.toNat_natCast, ← List.length_drop, List.take_length] at hyd
    have ht := hxt.trans hyt.symm
    have hd := hxd.trans hyd.symm
    have := congrArg₂ (fun a b : List U8 => a ++ b) ht hd
    simpa only [List.take_append_drop] using this
  · exact hk.symm

theorem lengths_unique (s cl x y : List U8) (i p j k : ℤ)
    (hlen : x.length = y.length)
    (hprefix : ∀ q : ℤ, 0 ≤ q → q < p → x[q.toNat]! = y[q.toNat]!)
    (hx : lengths_spec s i cl p x j) (hy : lengths_spec s i cl p y k) :
    x = y ∧ j = k := by
  generalize hm : ((x.length : ℤ) - p).toNat = m
  induction m using Nat.strong_induction_on generalizing i p j k with
  | h m ih =>
    rw [lengths_spec] at hx hy
    have hp := hx.1
    have hpx := hx.2 hp
    have hpy := hy.2 (by simpa only [lengths_pre, ← hlen] using hp)
    by_cases hend : p = x.length
    · constructor
      · apply list_eq x y hlen
        intro q hq
        simpa using hprefix q (by omega) (by omega)
      · exact (hpx.1 hend).trans (hpy.1 (by omega)).symm
    have hpx := hpx.2 hend
    have hpy := hpy.2 (by omega)
    simp only [guard_and] at hpx hpy
    obtain ⟨sym, a, n, hs, ha, hxb⟩ := hpx
    obtain ⟨sym', a', n', hs', ha', hyb⟩ := hpy
    have he := symbol_unique s cl i sym sym' hs hs'
    subst sym'
    rw [← ha] at ha'
    subst a'
    have recur (b v : ℤ) (hv : 0 < v) (hbound : p + v ≤ x.length)
        (hnew : ∀ q : ℤ, p ≤ q → q < p + v → x[q.toNat]! = y[q.toNat]!)
        (hx' : lengths_spec s b cl (p + v) x j)
        (hy' : lengths_spec s b cl (p + v) y k) : x = y ∧ j = k := by
      apply ih ((x.length : ℤ) - (p + v)).toNat ?_ b (p + v) j k ?_ hx' hy' rfl
      · clear hx hy hxb hyb hs hs'
        unfold lengths_pre at hp
        omega
      · intro q hq hq'
        by_cases hqp : q < p
        · exact hprefix q hq hqp
        · exact hnew q (by omega) hq'
    by_cases hlit : sym < 16
    · obtain ⟨hn, hvals, hx'⟩ := hxb.1 hlit
      obtain ⟨hn', hvals', hy'⟩ := hyb.1 hlit
      subst n; subst n'
      have hbound : p + 1 ≤ x.length := by unfold lengths_pre at hp; omega
      apply recur a 1 (by omega) hbound ?_ hx' hy'
      intro q hq hq'
      apply UScalar.eq_of_val_eq
      have := hvals q hq hq'
      have := hvals' q hq hq'
      omega
    have hxb := hxb.2 hlit
    have hyb := hyb.2 hlit
    by_cases h16 : sym = 16
    · obtain ⟨hp1, ⟨v, hv, hn⟩, hnb, hvals, hx'⟩ := hxb.1 h16
      obtain ⟨_, ⟨v', hv', hn'⟩, _, hvals', hy'⟩ := hyb.1 h16
      have he := field_unique s a 2 v v' hv hv'
      subst v'
      rw [← hn] at hn'
      subst n'
      apply recur (a + 2) n (by omega) hnb.2 ?_ hx' hy'
      intro q hq hq'
      rw [hvals q hq hq', hvals' q hq hq']
      exact hprefix (p - 1) (by omega) (by omega)
    have hxb := hxb.2 h16
    have hyb := hyb.2 h16
    by_cases h17 : sym = 17
    · obtain ⟨⟨v, hv, hn⟩, hnb, hvals, hx'⟩ := hxb.1 h17
      obtain ⟨⟨v', hv', hn'⟩, _, hvals', hy'⟩ := hyb.1 h17
      have he := field_unique s a 3 v v' hv hv'
      subst v'
      rw [← hn] at hn'
      subst n'
      apply recur (a + 3) n (by omega) hnb.2 ?_ hx' hy'
      intro q hq hq'
      apply UScalar.eq_of_val_eq
      have := hvals q hq hq'
      have := hvals' q hq hq'
      omega
    · obtain ⟨_, ⟨v, hv, hn⟩, hnb, hvals, hx'⟩ := hxb.2 h17
      obtain ⟨_, ⟨v', hv', hn'⟩, _, hvals', hy'⟩ := hyb.2 h17
      have he := field_unique s a 7 v v' hv hv'
      subst v'
      rw [← hn] at hn'
      subst n'
      apply recur (a + 7) n (by omega) hnb.2 ?_ hx' hy'
      intro q hq hq'
      apply UScalar.eq_of_val_eq
      have := hvals q hq hq'
      have := hvals' q hq hq'
      omega

def clOrder : List U8 :=
  [16#u8, 17#u8, 18#u8, 0#u8, 8#u8, 7#u8, 9#u8, 6#u8, 10#u8, 5#u8,
   11#u8, 4#u8, 12#u8, 3#u8, 13#u8, 2#u8, 14#u8, 1#u8, 15#u8]

theorem clOrder_covers : ∀ q : Fin 19, ∃ k : Fin 19, (clOrder[k.val]!).val = q.val := by decide

theorem tables_unique (s lit dist lit' dist' : List U8) (i j k : ℤ)
    (hx : tables_spec s i lit dist j) (hy : tables_spec s i lit' dist' k) :
    lit = lit' ∧ dist = dist' ∧ j = k := by
  obtain ⟨_, hclen, cl, all, ⟨v, hv, hll⟩, ⟨w, hw, hdl⟩, ⟨z, hz, hhc⟩,
    hcl, hvals, _, hall, hlt, hdt, hls, _, _⟩ := hx
  obtain ⟨_, hclen', cl', all', ⟨v', hv', hll'⟩, ⟨w', hw', hdl'⟩, ⟨z', hz', hhc'⟩,
    hcl', hvals', _, hall', hlt', hdt', hls', _, _⟩ := hy
  have he := field_unique _ _ _ _ _ hv hv'
  subst v'
  have he := field_unique _ _ _ _ _ hw hw'
  subst w'
  have he := field_unique _ _ _ _ _ hz hz'
  subst z'
  rw [← hhc] at hhc'
  subst hclen'
  have hlitlen : lit.length = lit'.length := by omega
  have hdistlen : dist.length = dist'.length := by omega
  have hcleq : cl = cl' := by
    apply list_eq cl cl' (by omega)
    intro q hq
    obtain ⟨r, hr⟩ := clOrder_covers ⟨q, by omega⟩
    have hr0 : (0 : ℤ) ≤ r.val := by omega
    have hr19 : (r.val : ℤ) < 19 := by have := r.isLt; omega
    have ha := hvals r.val hr0 hr19
    have hb := hvals' r.val hr0 hr19
    change ((clOrder[r.val]!).val = q) at hr
    change ((↑r.val < hclen → ∃ v, field_spec s (i + 14 + 3 * r.val) 3 v ∧ v = ((cl[(clOrder[r.val]!).val]!).val : ℤ)) ∧
      (¬ ↑r.val < hclen → ((cl[(clOrder[r.val]!).val]!).val : ℤ) = 0)) at ha
    change ((↑r.val < hclen → ∃ v, field_spec s (i + 14 + 3 * r.val) 3 v ∧ v = ((cl'[(clOrder[r.val]!).val]!).val : ℤ)) ∧
      (¬ ↑r.val < hclen → ((cl'[(clOrder[r.val]!).val]!).val : ℤ) = 0)) at hb
    rw [hr] at ha hb
    apply UScalar.eq_of_val_eq
    by_cases hrc : (r.val : ℤ) < hclen
    · obtain ⟨v, hv, he⟩ := ha.1 hrc
      obtain ⟨v', hv', he'⟩ := hb.1 hrc
      have := field_unique _ _ _ _ _ hv hv'
      omega
    · have := ha.2 hrc
      have := hb.2 hrc
      omega
  subst cl'
  have he := lengths_unique s cl all all' (i + 14 + 3 * hclen) 0 j k
    (by omega) (by intros; omega) hls hls'
  obtain ⟨he, hj⟩ := he
  subst all'
  have hlit : lit = lit' := by rw [← hlt, ← hlt', hlitlen]
  have hdist : dist = dist' := by rw [← hdt, ← hdt', hlitlen]
  exact ⟨hlit, hdist, hj⟩

theorem block_unique (s prev x y : List U8) (i j k : ℤ)
    (hx : block_spec s i prev x j) (hy : block_spec s i prev y k) :
    x = y ∧ j = k := by
  by_cases h0 : field_spec s i 2 0
  · exact stored_unique s prev x y (i + 2) j k (hx.2.1 h0) (hy.2.1 h0)
  by_cases h1 : field_spec s i 2 1
  · obtain ⟨lit, hlit, dist, hdist, hx⟩ := (hx.2.2 h0).1 h1
    obtain ⟨lit', hlit', dist', hdist', hy⟩ := (hy.2.2 h0).1 h1
    have he := fixedlit_unique lit lit' hlit hlit'
    subst lit'
    have he := fixeddist_unique dist dist' hdist hdist'
    subst dist'
    exact symbols_unique s lit dist prev x y (i + 2) j k hx hy
  · obtain ⟨_, lit, dist, a, ht, hx⟩ := (hx.2.2 h0).2 h1
    obtain ⟨_, lit', dist', a', ht', hy⟩ := (hy.2.2 h0).2 h1
    obtain ⟨he, hf, hg⟩ := tables_unique s lit dist lit' dist' (i + 2) a a' ht ht'
    subst lit'; subst dist'; subst a'
    exact symbols_unique s lit dist prev x y a j k hx hy

theorem blocks_unique (s prev x y : List U8) (i j k : ℤ)
    (hx : blocks_spec s i prev x j) (hy : blocks_spec s i prev y k) :
    x = y ∧ j = k := by
  generalize hm : (8 * (s.length : ℤ) - i).toNat = m
  induction m using Nat.strong_induction_on generalizing i prev x y j k with
  | h m ih =>
    rw [blocks_spec] at hx hy
    simp only [blocks_pre, true_and, forall_true_left, guard_and] at hx hy
    by_cases h0 : bit_spec s i 0
    · obtain ⟨mid, a, hb, ha, hx⟩ := hx.1 h0
      obtain ⟨mid', a', hb', ha', hy⟩ := hy.1 h0
      obtain ⟨he, hf⟩ := block_unique s prev mid mid' (i + 1) a a' hb hb'
      subst mid'; subst a'
      exact ih _ (hm ▸ bit_measure_decreases s i a ha.1 ha.2) _ _ _ _ _ _ hx hy rfl
    · exact block_unique s prev x y (i + 1) j k (hx.2 h0) (hy.2 h0)

theorem zero_unique (s : List U8) (i x y : ℤ)
    (hx : zero_spec s i x) (hy : zero_spec s i y) : x = y := by
  rcases _root_.lt_trichotomy x y with h | h | h
  · exact (hy.2.2.2 x hx.2.1.1.2 h hx.2.2.1).elim
  · exact h
  · exact (hx.2.2.2 y hy.2.1.1.2 h hy.2.2.1).elim

theorem header_unique (s : List U8) (x y : ℤ)
    (hx : header_spec s x) (hy : header_spec s y) : x = y := by
  obtain ⟨_, _, _, _, a, b, c, ha, hb, hc, hx, _⟩ := hx
  obtain ⟨_, _, _, _, a', b', c', ha', hb', hc', hy, _⟩ := hy
  have he : a = a' := by
    by_cases hf : flag_spec ((s[3]!).val : ℤ) 2 true
    · obtain ⟨v, hv, he⟩ := ha.1 hf
      obtain ⟨v', hv', he'⟩ := ha'.1 hf
      have := u16_unique s 10 v v' hv hv'
      omega
    · exact (ha.2 hf).trans (ha'.2 hf).symm
  subst a'
  have he : b = b' := by
    by_cases hf : flag_spec ((s[3]!).val : ℤ) 3 true
    · obtain ⟨v, hv, he⟩ := hb.1 hf
      obtain ⟨v', hv', he'⟩ := hb'.1 hf
      have := zero_unique s a v v' hv hv'
      omega
    · exact (hb.2 hf).trans (hb'.2 hf).symm
  subst b'
  have he : c = c' := by
    by_cases hf : flag_spec ((s[3]!).val : ℤ) 4 true
    · obtain ⟨v, hv, he⟩ := hc.1 hf
      obtain ⟨v', hv', he'⟩ := hc'.1 hf
      have := zero_unique s b v v' hv hv'
      omega
    · exact (hc.2 hf).trans (hc'.2 hf).symm
  subst c'
  by_cases hf : flag_spec ((s[3]!).val : ℤ) 1 true
  · exact (hx.1 hf).trans (hy.1 hf).symm
  · exact (hx.2 hf).trans (hy.2 hf).symm

theorem member_unique (s x y : List U8)
    (hx : member_spec s x) (hy : member_spec s y) : x = y := by
  obtain ⟨_, h, j, t, hh, hb, _⟩ := hx
  obtain ⟨_, h', j', t', hh', hb', _⟩ := hy
  have he := header_unique s h h' hh hh'
  subst h'
  exact (blocks_unique s [] x y (8 * h) j j' hb hb').1

end Gzip.Proofs.Decode.Parsing
