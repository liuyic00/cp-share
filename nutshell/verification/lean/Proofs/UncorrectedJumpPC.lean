import Proofs.PredictionPipeline
import Proofs.JalCommitPC
import Proofs.JalrCommitPC
namespace NutShellProofs
open nNutCore

theorem temporary_pc32_uncorrected_jump_target (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) (operation : JumpOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump operation (EXUPair (run initial inputs (t + 1))).1)
    (accepted : v12218 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    v12212 (run initial inputs (t + 1)) (inputs (t + 1)) =
      (WBUPair (run initial inputs (t + 2))).2 + 4 := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have op := ((jump_decode_run initial inputs reset t).2 valid operation matched unit).1
  have target := accepted_jump_prediction_target _ _ operation _ op accepted
  have prediction := (temporary_pc32_prediction_pipeline_run initial inputs reset environment restriction t).2.2 valid
  change v12215 (run initial inputs (t + 1)) (inputs (t + 1)) =
    (EXUPair (run initial inputs (t + 1))).2 + 4 at prediction
  have pair := committed_pair_is_execute_pair _ _ _ commit
  change WBUPair (run initial inputs (t + 2)) = _ at pair
  rw [pair]
  exact target.trans prediction

theorem temporary_pc32_reference_uncorrected_jump_commit (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) (operation : JumpOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump operation (EXUPair (run initial inputs (t + 1))).1)
    (accepted : v12218 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (reference : (run initial inputs (t + 3)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc =
      extendOperandPC (v12212 (run initial inputs (t + 1)) (inputs (t + 1)))) :
    RetirementReferenceAligned (run initial inputs (t + 3)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have op := ((jump_decode_run initial inputs reset t).2 valid operation matched unit).1
  have noTrap := jump_no_trap_run initial inputs reset environment t operation valid unit matched
  have redirect := (committed_jump_redirect_valid _ _ _ operation _ op commit unit noTrap).trans accepted
  change v8 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 at redirect
  have noRedirect : v14 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 := by
    simp [v14, v13, v12, v11, v10, redirect]
  have cursor := temporary_pc32_retirement_cursor_step initial inputs reset environment restriction (t + 1)
    currentReset noRedirect
  have target := temporary_pc32_uncorrected_jump_target initial inputs reset environment restriction t operation
    commit unit matched accepted
  unfold RetirementReferenceAligned
  rw [cursor]
  simp only [commit, ↓reduceIte]
  rw [retirement_cursor_committed _ _ commit, reference, target]

#print axioms temporary_pc32_uncorrected_jump_target
#print axioms temporary_pc32_reference_uncorrected_jump_commit

theorem temporary_pc32_reference_jal_commit (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump .jal (EXUPair (run initial inputs (t + 1))).1)
    (aligned : RetirementReferenceAligned (run initial inputs (t + 2)))
    : RetirementReferenceAligned (run initial inputs (t + 3)) := by
  rcases BitVec.eq_zero_or_eq_one (v12218 (run initial inputs (t + 1)) (inputs (t + 1))) with accepted | corrected
  · exact temporary_pc32_reference_uncorrected_jump_commit initial inputs reset environment restriction t .jal
      currentReset commit unit matched accepted
      (jal_reference_pc_full_update initial inputs reset t environment currentReset commit unit matched aligned)
  · exact reference_jal_corrected_commit initial inputs reset t environment currentReset commit unit matched aligned corrected

#print axioms temporary_pc32_reference_jal_commit

theorem temporary_pc32_reference_jalr_commit (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump .jalr (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    : RetirementReferenceAligned (run initial inputs (t + 3)) := by
  rcases BitVec.eq_zero_or_eq_one (v12218 (run initial inputs (t + 1)) (inputs (t + 1))) with accepted | corrected
  · exact temporary_pc32_reference_uncorrected_jump_commit initial inputs reset environment restriction t .jalr
      currentReset commit unit matched accepted
      (jalr_reference_pc_full_update initial inputs reset t environment currentReset commit unit matched registers)
  · exact reference_jalr_corrected_commit initial inputs reset t environment currentReset commit unit matched registers corrected

#print axioms temporary_pc32_reference_jalr_commit
end NutShellProofs
