import Proofs.JumpTargetWidth
import Proofs.JumpRecoveryRun
namespace NutShellProofs
open nNutCore

theorem jal_reference_pc_full_update (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump .jal (EXUPair (run initial inputs (t + 1))).1)
    (aligned : RetirementReferenceAligned (run initial inputs (t + 2))) :
    (run initial inputs (t + 3)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc =
      extendOperandPC (v12212 (run initial inputs (t + 1)) (inputs (t + 1))) := by
  have pc := task10_of_retirement_reference _ (inputs (t + 2)) aligned
  have mask : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&& (127 : BitVec 32) = 111 := by
    have instruction := committed_reference_instruction _ _ _ commit
    change v14575 (run initial inputs (t + 2)) (inputs (t + 2)) =
      BitVec.extractLsb' 0 32 (EXUPair (run initial inputs (t + 1))).1 at instruction
    rw [instruction]
    exact jump_match_low32 .jal _ matched
  have ok := reference_jump_jal_alignment _ _
    (jal_reference_sum_aligned_run initial inputs reset t (environment (t + 1)) currentReset commit unit matched pc)
  have updated := reference_jal_pc_update _ _ currentReset commit mask ok
  change (run initial inputs (t + 3)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc = _ at updated
  rw [updated, jal_target_matches_reference_node_run initial inputs reset t
    currentReset commit unit matched pc]
  exact (extend_operand_low39_upper_zero _
    (jal_reference_target_upper_zero initial inputs reset t environment currentReset commit unit matched pc)).symm

theorem reference_jal_corrected_commit (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump .jal (EXUPair (run initial inputs (t + 1))).1)
    (aligned : RetirementReferenceAligned (run initial inputs (t + 2)))
    (correction : v12218 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    RetirementReferenceAligned (run initial inputs (t + 3)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have noTrap := jump_no_trap_run initial inputs reset environment t .jal valid unit matched
  have op := ((jump_decode_run initial inputs reset t).2 valid .jal matched unit).1
  have redirected := (committed_jump_redirect_valid _ _ _ .jal _ op commit unit noTrap).trans correction
  change v8 (run initial inputs (t + 2)) (inputs (t + 2)) = 1 at redirected
  have flush : v14 (run initial inputs (t + 2)) (inputs (t + 2)) = 1 := by
    simp [v14, v13, v12, v11, v10, redirected, commit]
  have target := committed_alu_redirect_target _ _ _ commit unit noTrap
  change v2709 (run initial inputs (t + 2)) (inputs (t + 2)) = _ at target
  have cursor := retirement_cursor_redirect _ _ currentReset flush
  change RetirementCursor (run initial inputs (t + 3)) = _ at cursor
  unfold RetirementReferenceAligned
  rw [cursor, target]
  exact (jal_reference_pc_full_update initial inputs reset t environment currentReset commit unit matched aligned).symm

#print axioms jal_reference_pc_full_update
#print axioms reference_jal_corrected_commit
end NutShellProofs
