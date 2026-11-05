import Proofs.TemporaryPCStep
import Proofs.TemporaryRegisterInvariant
namespace NutShellProofs
open nNutCore

/-- Simultaneous induction closes PC/register correspondence without assuming task 10. -/
theorem temporary_pc32_joint_invariant (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) :
    ArchitecturalRegistersAligned (run initial inputs (t + 1)) ∧
      RetirementReferenceAligned (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact ⟨registers_aligned_after_reset _ _ reset, retirement_reference_reset _ _ reset⟩
  | succ t ih =>
    cases t with
    | zero =>
      have idle : v9 (run initial inputs 1) (inputs 1) = 0 := reset_has_no_next_commit _ _ _ reset
      rcases BitVec.eq_zero_or_eq_one (inputs 1).g0.nreset with currentReset | currentReset
      · exact ⟨registers_aligned_hold _ _ currentReset idle ih.1,
          temporary_pc32_retirement_reference_idle initial inputs reset environment restriction 0 currentReset idle ih.2⟩
      · exact ⟨registers_aligned_after_reset _ _ currentReset, retirement_reference_reset _ _ currentReset⟩
    | succ t =>
      exact ⟨temporary_pc32_registers_preserved_step initial inputs reset environment restriction t ih.1
          (task10_of_retirement_reference _ _ ih.2),
        temporary_pc32_pc_preserved_step initial inputs reset environment restriction t ih.1 ih.2⟩

theorem temporary_pc32_task10_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) :
    TaskHolds 10 (run initial inputs t) (inputs t) := by
  cases t with
  | zero => exact (asserts_iff_tasks _ _).mp (assertions_during_reset _ _ reset) 10
  | succ t =>
    exact task10_of_retirement_reference _ _
      (temporary_pc32_joint_invariant initial inputs reset environment restriction t).2

#print axioms temporary_pc32_joint_invariant
#print axioms temporary_pc32_task10_run
end NutShellProofs
