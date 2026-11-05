import Proofs.BranchTargetWidth
import Proofs.BranchRecoveryRun
import Proofs.PredictionPipeline
namespace NutShellProofs
open nNutCore

theorem branch_reference_pc_full_update (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (aligned : RetirementReferenceAligned (run initial inputs (t + 2))) :
    (run initial inputs (t + 3)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc =
      extendOperandPC (v12212 (run initial inputs (t + 1)) (inputs (t + 1))) := by
  have pc := task10_of_retirement_reference _ (inputs (t + 2)) aligned
  rw [branch_next_pc_matches_reference_run initial inputs reset t operation currentReset
    (environment (t + 1)) commit unit matched registers pc]
  have updated := reference_branch_pc_run initial inputs reset t operation currentReset
    (environment (t + 1)) commit unit matched registers pc
  rw [updated]
  split
  · exact (branch_reference_target_full_width initial inputs reset restriction t operation
      currentReset commit matched pc).symm
  · have pcs := committed_operand_pc_from_task10 _ _ _ currentReset commit pc
    change extendOperandPC (EXUPair (run initial inputs (t + 1))).2 =
      v16457 (run initial inputs (t + 2)) (inputs (t + 2)) at pcs
    have high := (temporary_pc32_instruction_pipeline initial inputs reset restriction t).2.2
      (commit_requires_execute_valid _ _ _ commit)
    rw [← pcs, ← extend_pc32_add_four (EXUPair (run initial inputs (t + 1))).2 high]
    simp only [extendOperandPC, BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 39 ≤ 39),
      BitVec.extractLsb'_eq_self]

#print axioms branch_reference_pc_full_update

theorem temporary_pc32_reference_branch_commit (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (aligned : RetirementReferenceAligned (run initial inputs (t + 2))) :
    RetirementReferenceAligned (run initial inputs (t + 3)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have op := ((branch_decode_run initial inputs reset t).2 valid operation matched unit).1
  have noTrap := branch_no_trap_run initial inputs reset environment t operation valid unit matched
  have redirect := committed_branch_redirect_valid _ _ _ operation op commit unit noTrap
  change v8 (run initial inputs (t + 2)) (inputs (t + 2)) = _ at redirect
  have reference := branch_reference_pc_full_update initial inputs reset environment restriction t operation
    currentReset commit unit matched registers aligned
  rcases BitVec.eq_zero_or_eq_one (v12218 (run initial inputs (t + 1)) (inputs (t + 1))) with accepted | corrected
  · have noRedirect : v14 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 := by
      simp [v14, v13, v12, v11, v10, redirect.trans accepted]
    have target : v12212 (run initial inputs (t + 1)) (inputs (t + 1)) =
        (EXUPair (run initial inputs (t + 1))).2 + 4 := by
      rcases BitVec.eq_zero_or_eq_one (v12179 (run initial inputs (t + 1)) (inputs (t + 1))) with untaken | taken
      · have branch : v12182 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 := by
          cases operation <;> simp [v12182, v12181, v12141, v28, op, BranchOp.control, v24]
        simpa [v12212, v12190, v12189, branch, untaken, v24] using
          branch_sequential_pc (run initial inputs (t + 1)) (inputs (t + 1)) operation matched
      · have predicted := (accepted_taken_branch_prediction _ _ operation op taken accepted).2
        exact predicted.trans ((temporary_pc32_prediction_pipeline_run initial inputs reset environment restriction t).2.2 valid)
    have cursor := temporary_pc32_retirement_cursor_step initial inputs reset environment restriction (t + 1)
      currentReset noRedirect
    have pair := committed_pair_is_execute_pair _ _ _ commit
    change WBUPair (run initial inputs (t + 2)) = _ at pair
    unfold RetirementReferenceAligned
    rw [cursor]
    simp only [commit, ↓reduceIte]
    rw [retirement_cursor_committed _ _ commit, pair, reference, target]
  · have flush : v14 (run initial inputs (t + 2)) (inputs (t + 2)) = 1 := by
      simp [v14, v13, v12, v11, v10, redirect.trans corrected, commit]
    have target := committed_alu_redirect_target _ _ _ commit unit noTrap
    change v2709 (run initial inputs (t + 2)) (inputs (t + 2)) = _ at target
    have cursor := retirement_cursor_redirect _ _ currentReset flush
    change RetirementCursor (run initial inputs (t + 3)) = _ at cursor
    unfold RetirementReferenceAligned
    rw [cursor, target, reference]

#print axioms temporary_pc32_reference_branch_commit
end NutShellProofs
