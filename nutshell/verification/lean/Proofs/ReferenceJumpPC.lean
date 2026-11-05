import Proofs.ReferenceJumpAlignment
import Proofs.ReferencePCUpdate
namespace NutShellProofs
open nNutCore

theorem reference_jal_pc_update (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (127 : BitVec 32) = 111)
    (aligned : v16484 s i = 1) :
    (step s i).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc = v23598 s i := by
  rw [reference_pc_update_normal s i reset commit
    (reference_jump_jal_no_exception s i matched aligned)
    (reference_jump_imm_jal_not_v14595 s i matched)
    (reference_jump_imm_jal_not_v14601 s i matched),
    reference_jump_jal_redirect s i matched aligned,
    reference_jump_jal_selection s i matched aligned]
  simp
#print axioms reference_jal_pc_update

theorem reference_jalr_pc_update (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& (28799 : BitVec 32) = 103)
    (aligned : v16454 s i = 1) :
    (step s i).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc = v23594 s i := by
  rw [reference_pc_update_normal s i reset commit
    (reference_jump_jalr_no_exception s i matched aligned)
    (reference_jump_imm_jalr_not_v14595 s i matched)
    (reference_jump_imm_jalr_not_v14601 s i matched),
    reference_jump_jalr_redirect s i matched aligned,
    reference_jump_jalr_selection s i matched aligned]
  simp
#print axioms reference_jalr_pc_update

theorem jal_target_matches_updated_reference_pc_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (environment : assumes (run initial inputs (t + 1)) (inputs (t + 1)))
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump .jal (EXUPair (run initial inputs (t + 1))).1)
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2))) :
    v12212 (run initial inputs (t + 1)) (inputs (t + 1)) =
      BitVec.extractLsb' 0 39
        (run initial inputs (t + 3)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc := by
  have mask : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&& (127 : BitVec 32) = 111 := by
    have instruction := committed_reference_instruction _ _ _ commit
    change v14575 (run initial inputs (t + 2)) (inputs (t + 2)) =
      BitVec.extractLsb' 0 32 (EXUPair (run initial inputs (t + 1))).1 at instruction
    rw [instruction]
    exact jump_match_low32 .jal _ matched
  have ok := reference_jump_jal_alignment _ _
    (jal_reference_sum_aligned_run initial inputs reset t environment currentReset commit unit matched pc)
  have updated := reference_jal_pc_update _ _ currentReset commit mask ok
  change (run initial inputs (t + 3)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc = _ at updated
  rw [updated]
  exact jal_target_matches_reference_node_run initial inputs reset t currentReset commit unit matched pc
#print axioms jal_target_matches_updated_reference_pc_run

theorem jalr_target_matches_updated_reference_pc_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (environment : assumes (run initial inputs (t + 1)) (inputs (t + 1)))
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump .jalr (EXUPair (run initial inputs (t + 1))).1)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    v12212 (run initial inputs (t + 1)) (inputs (t + 1)) =
      BitVec.extractLsb' 0 39
        (run initial inputs (t + 3)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc := by
  have mask : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&& (28799 : BitVec 32) = 103 := by
    have instruction := committed_reference_instruction _ _ _ commit
    change v14575 (run initial inputs (t + 2)) (inputs (t + 2)) =
      BitVec.extractLsb' 0 32 (EXUPair (run initial inputs (t + 1))).1 at instruction
    rw [instruction]
    exact jump_match_low32 .jalr _ matched
  have ok := reference_jump_jalr_alignment _ _
    (jalr_reference_sum_aligned_run initial inputs reset t environment commit unit matched aligned)
  have updated := reference_jalr_pc_update _ _ currentReset commit mask ok
  change (run initial inputs (t + 3)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc = _ at updated
  rw [updated]
  exact jalr_target_matches_reference_node_run initial inputs reset t environment commit unit matched aligned
#print axioms jalr_target_matches_updated_reference_pc_run
end NutShellProofs
