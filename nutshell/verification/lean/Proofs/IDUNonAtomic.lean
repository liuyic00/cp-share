import Proofs.WhitelistNoAtomics
namespace NutShellProofs
open nNutCore

def NonAtomicInstruction (x : BitVec 64) : Prop := BitVec.extractLsb' 0 7 x ≠ 47

def IDUNonAtomic (s : State) : Prop :=
  s.g38.r1241_nfrontend_5Fvalid = 1 →
    NonAtomicInstruction s.g38.r1242_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Finstr

theorem idu_non_atomic_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    IDUNonAtomic (step s i) := by
  intro valid
  change v11101 s i = 1 at valid
  simp [v11101, v0, v24, reset] at valid

theorem idu_non_atomic_step (s : State) (i : Inputs) (old : IDUNonAtomic s) (environment : assumes s i) :
    IDUNonAtomic (step s i) := by
  intro valid
  change NonAtomicInstruction (v11106 s i)
  by_cases fire : v11102 s i = 1
  · rw [v11106, if_pos fire]
    have noReset : i.g0.nreset = 0 := by
      rcases BitVec.eq_zero_or_eq_one i.g0.nreset with zero | one
      · exact zero
      · change v11101 s i = 1 at valid
        simp [v11101, v0, v24, one] at valid
    have inputValid : v10100 s i = 1 := by
      rcases BitVec.eq_zero_or_eq_one (v10100 s i) with zero | one
      · simp [v11102, zero] at fire
      · exact one
    have excluded := original_whitelist_excludes_atomic s i environment noReset inputValid
    simpa only [NonAtomicInstruction, v30884, v11105, v11104,
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 32 ≤ 32),
      BitVec.extractLsb'_eq_self,
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 7 ≤ 32)] using excluded
  · rw [v11106, if_neg fire]
    apply old
    have noCapture : v11096 s i ≠ 1 := fire
    change v11101 s i = 1 at valid
    unfold v11101 at valid
    split at valid
    · simp [v24] at valid
    · unfold v11100 at valid
      split at valid
      · simp [v24] at valid
      · simp only [v11099, noCapture, ↓reduceIte] at valid
        unfold v11098 at valid
        split at valid
        · simp [v24] at valid
        · exact valid


theorem idu_non_atomic_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ t, assumes (run initial inputs t) (inputs t)) (t : Nat) :
    IDUNonAtomic (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact idu_non_atomic_reset initial (inputs 0) reset
  | succ t ih => exact idu_non_atomic_step _ _ ih (environment (t + 1))

#print axioms idu_non_atomic_run
end NutShellProofs
