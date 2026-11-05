import Proofs.RetirementCursor
import Proofs.ReferencePCHold
namespace NutShellProofs
open nNutCore

/-- Full-width equality required by the original PC assertion. -/
def RetirementReferenceAligned (s : State) : Prop :=
  extendOperandPC (RetirementCursor s) =
    s.g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc

theorem task10_of_retirement_reference (s : State) (i : Inputs)
    (aligned : RetirementReferenceAligned s) : TaskHolds 10 s i := by
  change decide (v31361 s i ≠ 1 ∨ v31359 s i = 1) = true
  apply decide_eq_true
  rcases BitVec.eq_zero_or_eq_one (v9 s i) with idle | commit
  · left
    simp [v31361, v14558, idle]
  · right
    have cursor := retirement_cursor_committed s i commit
    have compare : v31357 s i = v31358 s i := by
      change extendOperandPC (WBUPair s).2 = _
      rw [← cursor]
      exact aligned
    simp [v31359, compare]

theorem retirement_reference_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    RetirementReferenceAligned (step s i) := by
  unfold RetirementReferenceAligned
  rw [retirement_cursor_reset s i reset]
  change extendOperandPC 0x80000000 = v23683 s i
  simp [v23683, v14555, v14554, v14553, v11455, reset, v15706, extendOperandPC]

theorem temporary_pc32_retirement_reference_idle (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (currentReset : (inputs (t + 1)).g0.nreset = 0)
    (idle : v9 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (aligned : RetirementReferenceAligned (run initial inputs (t + 1))) :
    RetirementReferenceAligned (run initial inputs (t + 2)) := by
  have noRedirect : v14 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := by
    simp [v14, v13, v12, v11, v10, idle]
  have cursor := temporary_pc32_retirement_cursor_step initial inputs reset environment restriction t currentReset noRedirect
  simp only [idle, show (0 : BitVec 1) ≠ 1 by decide, ↓reduceIte] at cursor
  have reference := reference_pc_hold (run initial inputs (t + 1)) (inputs (t + 1)) currentReset idle
  change (run initial inputs (t + 2)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc = _ at reference
  unfold RetirementReferenceAligned
  rw [cursor, reference]
  exact aligned

#print axioms task10_of_retirement_reference
#print axioms retirement_reference_reset
#print axioms temporary_pc32_retirement_reference_idle
end NutShellProofs
