import Gzip.Proofs.Decode.TablesImpl

open Aeneas Std Result
open Gzip.Spec Gzip.Proofs.Decode.Encoding

namespace Gzip.Proofs.Decode.BaseTables

theorem length_table (k : Nat) (hk : k ≤ 28) :
    lbase_spec k lengthBases[k]! := by
  induction k with
  | zero => rw [lbase_spec]; norm_num [lbase_pre, lengthBases]
  | succ k ih =>
    by_cases he : k = 27
    · subst k; rw [lbase_spec]; norm_num [lbase_pre, lengthBases]
    have hkbound : k ≤ 26 := by omega
    have hprev := ih (by omega)
    rw [lbase_spec]
    refine ⟨by simp only [lbase_pre, dbase_pre]; omega, fun _ => ⟨by omega, fun _ => ⟨?_, ?_⟩⟩⟩
    · intro h; omega
    · intro _
      refine ⟨by intro h; omega, fun _ => ?_⟩
      refine ⟨lengthBases[k]!, ?_, (if k < 8 then 0 else k / 4 - 1 : Nat), ?_, ?_⟩
      · simpa using hprev
      · interval_cases k <;> norm_num [lextra_spec, lextra_pre]
      · interval_cases k <;> norm_num [lengthBases, Int.toNat]

theorem distance_table (k : Nat) (hk : k ≤ 29) :
    dbase_spec k distanceBases[k]! := by
  induction k with
  | zero => rw [dbase_spec]; norm_num [dbase_pre, distanceBases]
  | succ k ih =>
    have hkbound : k ≤ 28 := by omega
    have hprev := ih (by omega)
    rw [dbase_spec]
    refine ⟨by simp only [lbase_pre, dbase_pre]; omega, fun _ => ⟨by omega, fun _ => ⟨?_, ?_⟩⟩⟩
    · intro h; omega
    · intro _
      refine ⟨distanceBases[k]!, ?_, (if k < 4 then 0 else k / 2 - 1 : Nat), ?_, ?_⟩
      · simpa using hprev
      · interval_cases k <;> norm_num [dextra_spec, dextra_pre]
      · interval_cases k <;> norm_num [distanceBases, Int.toNat]

end Gzip.Proofs.Decode.BaseTables
