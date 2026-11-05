import Proofs.BranchTarget
import Proofs.ReferenceBranchConditions
import Proofs.CommittedBranchImmediate
import Proofs.AuipcCorrespondence
namespace NutShellProofs
open nNutCore

theorem branch_target_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2))) :
    v12211 (run initial inputs (t + 1)) (inputs (t + 1)) =
      BitVec.extractLsb' 0 39 (referenceBranchTarget operation
        (run initial inputs (t + 2)) (inputs (t + 2))) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have pcs := committed_operand_pc_from_task10 _ _ _ currentReset commit pc
  have imm := committed_reference_branch_immediate _ _ _ operation commit matched
  have refResult := reference_branch_target operation
    (step (run initial inputs (t + 1)) (inputs (t + 1))) (inputs (t + 2))
  rw [← pcs, imm] at refResult
  have low := congrArg (BitVec.extractLsb' 0 39) refResult
  simp only [low_add _ _ (by decide : 39 ≤ 64), extendOperandPC,
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 39 ≤ 39),
    BitVec.extractLsb'_eq_self] at low
  exact (branch_target_run initial inputs reset t operation valid unit matched).trans low.symm

#print axioms branch_target_matches_reference_run
end NutShellProofs
