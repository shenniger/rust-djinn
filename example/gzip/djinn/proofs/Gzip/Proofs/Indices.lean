import Gzip.Proofs.Costs
import Gzip.Spec

open Aeneas Std Result
open Gzip.solution Gzip.Spec

namespace Gzip.Proofs.Indices

def lb (i : ℕ) : ℕ := (LENGTH_BASE.val[i]!).val
def le (i : ℕ) : ℕ := (LENGTH_EXTRA.val[i]!).val
def db (i : ℕ) : ℕ := (DIST_BASE.val[i]!).val
def de (i : ℕ) : ℕ := (DIST_EXTRA.val[i]!).val

theorem length_gaps : ∀ i : Fin 28, lb (i.val + 1) ≤ lb i.val + 2 ^ le i.val := by
  rintro ⟨i, hi⟩
  interval_cases i <;> norm_num [lb, le, LENGTH_BASE, LENGTH_EXTRA, Array.make]
theorem distance_gaps : ∀ i : Fin 29, db (i.val + 1) = db i.val + 2 ^ de i.val := by
  rintro ⟨i, hi⟩
  interval_cases i <;> norm_num [db, de, DIST_BASE, DIST_EXTRA, Array.make]
theorem length_recurrence : ∀ i : Fin 27, lb (i.val + 1) = lb i.val + 2 ^ le i.val := by
  rintro ⟨i, hi⟩
  interval_cases i <;> norm_num [lb, le, LENGTH_BASE, LENGTH_EXTRA, Array.make]

theorem lextra_correct (i : ℕ) (hi : i < 29) : lextra_spec i (le i) := by
  interval_cases i <;> norm_num [lextra_spec, lextra_pre, le, LENGTH_EXTRA, Array.make]

theorem dextra_correct (i : ℕ) (hi : i < 30) : dextra_spec i (de i) := by
  interval_cases i <;> norm_num [dextra_spec, dextra_pre, de, DIST_EXTRA, Array.make]

theorem lbase_correct (i : ℕ) (hi : i < 29) : lbase_spec i (lb i) := by
  induction i with
  | zero =>
      rw [lbase_spec]
      norm_num [lbase_pre, lb, LENGTH_BASE, Array.make]
  | succ i ih =>
      rw [lbase_spec]
      refine ⟨by unfold lbase_pre; omega, fun _ => ⟨by omega, fun _ => ⟨fun hz => by omega, fun _ => ?_⟩⟩⟩
      by_cases hlast : i + 1 = 28
      · constructor
        · intro _
          rw [hlast]
          norm_num [lb, LENGTH_BASE, Array.make]
        · intro hn
          omega
      · refine ⟨fun he => by omega, fun _ => ?_⟩
        have hidx : ((i + 1 : ℕ) : ℤ) - 1 = i := by omega
        rw [hidx]
        refine ⟨lb i, ih (by omega), le i, lextra_correct i (by omega), ?_⟩
        have hr := length_recurrence ⟨i, by omega⟩
        simp only [Int.toNat_natCast, ← Nat.cast_pow, ← Nat.cast_add]
        exact congrArg (fun n : ℕ => (n : ℤ)) hr

theorem dbase_correct (i : ℕ) (hi : i < 30) : dbase_spec i (db i) := by
  induction i with
  | zero =>
      rw [dbase_spec]
      norm_num [dbase_pre, db, DIST_BASE, Array.make]
  | succ i ih =>
      rw [dbase_spec]
      refine ⟨by unfold dbase_pre; omega, fun _ => ⟨by omega, fun _ => ⟨fun hz => by omega, fun _ => ?_⟩⟩⟩
      have hidx : ((i + 1 : ℕ) : ℤ) - 1 = i := by omega
      rw [hidx]
      refine ⟨db i, ih (by omega), de i, dextra_correct i (by omega), ?_⟩
      have hr := distance_gaps ⟨i, by omega⟩
      simp only [Int.toNat_natCast, ← Nat.cast_pow, ← Nat.cast_add]
      exact congrArg (fun n : ℕ => (n : ℤ)) hr

theorem lb_get (i : Usize) (hi : i.val < 29) :
    (LENGTH_BASE.val[i.val]'(by simp [LENGTH_BASE, Array.make]; omega)).val = lb i.val := by
  unfold lb
  rw [getElem!_pos LENGTH_BASE.val i.val (by simp [LENGTH_BASE, Array.make]; omega)]

theorem db_get (i : Usize) (hi : i.val < 30) :
    (DIST_BASE.val[i.val]'(by simp [DIST_BASE, Array.make]; omega)).val = db i.val := by
  unfold db
  rw [getElem!_pos DIST_BASE.val i.val (by simp [DIST_BASE, Array.make]; omega)]

end Gzip.Proofs.Indices
