/-  Proofs.lean — the implementer's file. Written once by `cargo djinn
    translate`, never overwritten. Replace every `sorry`; add any helper
    lemmas you need (loop invariants, bridging lemmas) in this file. -/
import Aeneas
import AnyDemo.Spec
import AnyDemo.Vocab
import AnyDemo.Code.Funs

open Aeneas Std Result
open AnyDemo.Spec
open Djinn.Vocab

namespace AnyDemo.Proofs

/-! ## checked_div -/

theorem checked_div.unambiguous :
    ∀ (a : U32) (b : U32) (msg : U32 → U32 → List U8) (o₁ : core.result.Result U32 (List U8)) (o₂ : core.result.Result U32 (List U8)),
      checked_div_body a b msg o₁ → checked_div_body a b msg o₂ → o₁ = o₂ := by
  intro a b msg o₁ o₂ h₁ h₂
  by_cases hb : (b.val : ℤ) = 0
  · exact (h₁.2.1 hb).2.trans (h₂.2.1 hb).2.symm
  · obtain ⟨q₁, hq₁, rfl⟩ := h₁.2.2 hb
    obtain ⟨q₂, hq₂, rfl⟩ := h₂.2.2 hb
    have : q₁ = q₂ := (UScalar.eq_equiv _ _).mpr (by omega)
    rw [this]

theorem checked_div.wf :
    ∀ (a : U32) (b : U32) (msg : U32 → U32 → List U8) (out : core.result.Result U32 (List U8)),
      checked_div_body a b msg out →
      ¬((b.val : ℤ) = 0) → ∀ q : U32, ((q.val : ℤ) = ((a.val : ℤ) / (b.val : ℤ)) ∧ out = (.Ok q)) → ((b.val : ℤ) ≠ 0) := by
  intro a b msg out h hb q hq
  exact hb

/-! ## safe_div -/

theorem safe_div.unambiguous :
    ∀ (a : U32) (b : U32) (checked_div_msg : U32 → U32 → U32 → U32 → List U8) (checked_div_msg_1 : U32 → U32 → U32 → U32 → List U8) (o₁ : U32) (o₂ : U32),
      safe_div_body a b checked_div_msg checked_div_msg_1 o₁ → safe_div_body a b checked_div_msg checked_div_msg_1 o₂ → o₁ = o₂ := by
  intro a b m n o₁ o₂ h₁ h₂
  by_cases hb : (b.val : ℤ) = 0
  · apply (UScalar.eq_equiv _ _).mpr
    have := (h₁.2.1 hb).2
    have := (h₂.2.1 hb).2
    omega
  · obtain ⟨r₁, hr₁, rfl⟩ := h₁.2.2 hb
    obtain ⟨r₂, hr₂, rfl⟩ := h₂.2.2 hb
    exact core.result.Result.Ok.inj (checked_div.unambiguous a b (n a b) _ _ hr₁ hr₂)

theorem safe_div.ens_0 :
    ∀ (a : U32) (b : U32) (out : U32),
      safe_div_spec a b out → ((b.val : ℤ) ≠ 0 → (out.val : ℤ) = ((a.val : ℤ) / (b.val : ℤ))) := by
  intro a b out ⟨m, n, h⟩ hb
  obtain ⟨r, hr, rfl⟩ := h.2.2 hb
  obtain ⟨q, hq, heq⟩ := hr.2.2 hb
  cases heq
  exact hq

theorem safe_div.wf :
    ∀ (a : U32) (b : U32) (checked_div_msg : U32 → U32 → U32 → U32 → List U8) (checked_div_msg_1 : U32 → U32 → U32 → U32 → List U8) (out : U32),
      safe_div_body a b checked_div_msg checked_div_msg_1 out →
      (b.val : ℤ) ≠ 0 → ((b.val : ℤ) ≠ 0) := by
  intro a b m n out h hb
  exact hb

/-! ## shrink -/

theorem shrink.unambiguous :
    ∀ (v : List U8) (w : (List U8) → ℤ → U8) (o₁ : List U8) (o₂ : List U8),
      shrink_body v w o₁ → shrink_body v w o₂ → o₁ = o₂ := by
  intro v w o₁ o₂ h₁ h₂
  obtain ⟨_, hl₁, h₁⟩ := h₁
  obtain ⟨_, hl₂, h₂⟩ := h₂
  apply List.ext_getElem
  · omega
  · intro i hi hj
    have hiv : (i : ℤ) < (v.length : ℤ) := by omega
    have h₁i := (h₁ i (by omega) hiv).2
    have h₂i := (h₂ i (by omega) hiv).2
    simpa [getElem!_pos, hi, hj] using h₁i.trans h₂i.symm

theorem shrink.wf :
    ∀ (v : List U8) (w : (List U8) → ℤ → U8) (out : List U8),
      shrink_body v w out →
      (∀ i : ℤ, 0 ≤ i → i < (v.length : ℤ) → (0 ≤ i ∧ i < (v.length : ℤ))) ∧
      (∀ i : ℤ, 0 ≤ i → i < (v.length : ℤ) → (0 ≤ i ∧ i < (out.length : ℤ))) := by
  intro v w out h
  constructor <;> intro i hi hj
  · exact ⟨hi, hj⟩
  · have := h.2.1
    exact ⟨hi, by omega⟩

/-! ## pick -/

theorem pick.unambiguous :
    ∀ (lo : I32) (hi : I32) (k : I32 → I32 → I32) (o₁ : I32) (o₂ : I32),
      pick_body lo hi k o₁ → pick_body lo hi k o₂ → o₁ = o₂ := by
  intro lo hi k o₁ o₂ h₁ h₂
  exact h₁.2.2.trans h₂.2.2.symm

/-! ## pick_twice -/

theorem pick_twice.unambiguous :
    ∀ (lo : I32) (hi : I32) (pick_k : I32 → I32 → I32 → I32 → I32) (pick_k_1 : I32 → I32 → I32 → I32 → I32) (o₁ : I32) (o₂ : I32),
      pick_twice_body lo hi pick_k pick_k_1 o₁ → pick_twice_body lo hi pick_k pick_k_1 o₂ → o₁ = o₂ := by
  intro lo hi k l o₁ o₂ h₁ h₂
  obtain ⟨p₁, q₁, hp₁, hq₁, he₁⟩ := h₁.2
  obtain ⟨p₂, q₂, hp₂, hq₂, he₂⟩ := h₂.2
  have hq := pick.unambiguous lo hi (l lo hi) q₁ q₂ hq₁ hq₂
  apply (IScalar.eq_equiv _ _).mpr
  rw [hq] at he₁
  omega

theorem pick_twice.ens_0 :
    ∀ (lo : I32) (hi : I32) (out : I32),
      pick_twice_spec lo hi out → out.val ≥ lo.val := by
  intro lo hi out ⟨k, l, h⟩
  obtain ⟨p, q, hp, hq, he⟩ := h.2
  have hlow := hq.2.1.1
  rw [← hq.2.2] at hlow
  omega

theorem pick_twice.wf :
    ∀ (lo : I32) (hi : I32) (pick_k : I32 → I32 → I32 → I32 → I32) (pick_k_1 : I32 → I32 → I32 → I32 → I32) (out : I32),
      pick_twice_body lo hi pick_k pick_k_1 out →
      (∀ p : I32, ∀ q : I32, (pick_body lo hi (pick_k lo hi) p ∧ pick_body lo hi (pick_k_1 lo hi) q ∧ out.val = ((p.val + q.val) - p.val)) → (pick_pre lo hi)) ∧
      (∀ p : I32, ∀ q : I32, (pick_body lo hi (pick_k lo hi) p ∧ pick_body lo hi (pick_k_1 lo hi) q ∧ out.val = ((p.val + q.val) - p.val)) → (pick_pre lo hi)) := by
  intro lo hi k l out h
  constructor <;> intro p q hpq <;> exact hpq.1.1

def checked_div.msg (_a _b : U32) : List U8 := bytes "division by zero"

theorem checked_div.impl_correct :
    ∀ (a : U32) (b : U32), checked_div_pre a b →
      AnyDemo.spec.checked_div a b ⦃ out => checked_div_spec a b (match out with | .Ok y => .Ok y | .Err y => .Err (bytes y)) ⦄ := by
  intro a b hpre
  unfold AnyDemo.spec.checked_div AnyDemo.solution.checked_div
  split
  · rename_i hb
    subst b
    have hs : alloc.string.String.Insts.CoreConvertFromShared0Str.from
        (toStr "division by zero" (by rw [show Aeneas.Std.U32.max = 4294967295 by scalar_tac]; decide +kernel)) = ok "division by zero" := by
      unfold alloc.string.String.Insts.CoreConvertFromShared0Str.from
      have hs : ofBytes (toStr "division by zero" (by rw [show Aeneas.Std.U32.max = 4294967295 by scalar_tac]; decide +kernel)).val = some "division by zero" := by
        decide +kernel
      rw [hs]
    rw [hs]
    simp only [bind_ok, WP.spec_ok]
    refine ⟨checked_div.msg, ?_⟩
    simp [checked_div_body, checked_div_pre, checked_div.msg]
    decide
  · rename_i hb
    step as ⟨q, hq⟩
    refine ⟨checked_div.msg, ?_⟩
    have hbval : (b.val : ℤ) ≠ 0 := by scalar_tac
    simp only [checked_div_body, checked_div_pre]
    refine ⟨trivial, ?_, ?_⟩
    · exact fun h => False.elim (hbval h)
    · intro _
      exact ⟨q, by omega, rfl⟩

theorem safe_div.impl_correct :
    ∀ (a : U32) (b : U32), safe_div_pre a b →
      AnyDemo.spec.safe_div a b ⦃ out => safe_div_spec a b out ⦄ := by
  intro a b hpre
  have hc := checked_div.impl_correct a b trivial
  unfold AnyDemo.spec.checked_div at hc
  unfold AnyDemo.spec.safe_div AnyDemo.solution.safe_div
  rw [WP.spec_equiv_exists] at hc
  obtain ⟨r, hr, m, hm⟩ := hc
  rw [hr]
  cases r with
  | Ok q =>
    simp only [bind_ok, WP.spec_ok]
    refine ⟨fun _ _ => m, fun _ _ => m, trivial, ?_, ?_⟩
    · intro hb
      have he := (hm.2.1 hb).2
      cases he
    · intro _
      exact ⟨.Ok q, hm, rfl⟩
  | Err s =>
    simp only [bind_ok, WP.spec_ok]
    refine ⟨fun _ _ => m, fun _ _ => m, trivial, ?_, ?_⟩
    · intro _
      exact ⟨⟨bytes s, .Err (bytes s), hm, rfl⟩, by simp⟩
    · intro hb
      obtain ⟨q, _, he⟩ := hm.2.2 hb
      cases he

def pick.k (lo _hi : I32) : I32 := lo

theorem pick.impl_correct :
    ∀ (lo : I32) (hi : I32), pick_pre lo hi →
      AnyDemo.spec.pick lo hi ⦃ out => pick_spec lo hi out ⦄ := by
  intro lo hi hpre
  unfold AnyDemo.spec.pick AnyDemo.solution.pick
  simp only [WP.spec_ok]
  exact ⟨pick.k, hpre, ⟨_root_.le_refl _, hpre⟩, rfl⟩

theorem pick_twice.impl_correct :
    ∀ (lo : I32) (hi : I32), pick_twice_pre lo hi →
      AnyDemo.spec.pick_twice lo hi ⦃ out => pick_twice_spec lo hi out ⦄ := by
  intro lo hi hpre
  have hp := pick.impl_correct lo hi hpre
  unfold AnyDemo.spec.pick at hp
  unfold AnyDemo.spec.pick_twice AnyDemo.solution.pick_twice
  apply WP.spec_mono hp
  intro out ⟨k, hk⟩
  refine ⟨fun _ _ => k, fun _ _ => k, hpre, out, out, hk, hk, ?_⟩
  omega

def shrink.w (_v : List U8) (_i : ℤ) : U8 := 0#u8

def shrink.Inv (v : Aeneas.Std.Slice U8) (out : alloc.vec.Vec U8) (i : Usize) : Prop :=
  i.val ≤ v.val.length ∧ out.val = List.replicate i.val 0#u8

theorem shrink.loop_body (v : Aeneas.Std.Slice U8) (out : alloc.vec.Vec U8)
    (i : Usize) (hinv : shrink.Inv v out i) :
    AnyDemo.solution.shrink_loop.body v out i ⦃ r =>
      match r with
      | .done out' => out'.val = List.replicate v.val.length 0#u8
      | .cont x => shrink.Inv v x.1 x.2 ∧ v.val.length - x.2.val < v.val.length - i.val ⦄ := by
  obtain ⟨hi, hout⟩ := hinv
  unfold AnyDemo.solution.shrink_loop.body
  step*
  all_goals simp_all [shrink.Inv, List.replicate_succ']
  all_goals scalar_tac

@[step]
theorem shrink.loop_spec (v : Aeneas.Std.Slice U8) (out : alloc.vec.Vec U8)
    (i : Usize) (hinv : shrink.Inv v out i) :
    AnyDemo.solution.shrink_loop v out i ⦃ out' => out'.val = List.replicate v.val.length 0#u8 ⦄ := by
  unfold AnyDemo.solution.shrink_loop
  apply loop.spec_decr_nat (fun (_, i) => v.val.length - i.val)
    (fun (out, i) => shrink.Inv v out i)
  · rintro ⟨out', i'⟩ hinv'
    apply WP.spec_mono (shrink.loop_body v out' i' hinv')
    intro r hr
    cases r <;> exact hr
  · exact hinv

theorem shrink.impl_correct :
    ∀ (v : Aeneas.Std.Slice U8), shrink_pre v.val →
      AnyDemo.spec.shrink v ⦃ out => shrink_spec v.val out.val ⦄ := by
  intro v hpre
  unfold AnyDemo.spec.shrink AnyDemo.solution.shrink
  have hinv : shrink.Inv v (alloc.vec.Vec.new U8) 0#usize := by
    simp [shrink.Inv, alloc.vec.Vec.new]
  apply WP.spec_mono (shrink.loop_spec v _ _ hinv)
  intro out hout
  refine ⟨shrink.w, trivial, ?_, ?_⟩
  · simp [hout]
  · intro i hi hj
    constructor
    · simp [shrink.w]
    · have hidx : i.toNat < v.val.length := by omega
      simp [hout, shrink.w, getElem!_pos, hidx]

end AnyDemo.Proofs
