import Proofs.JumpLink
import Proofs.AuipcCorrespondence
namespace NutShellProofs
open nNutCore

theorem jump_writeback_reference_pc_plus_four_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : JumpOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump operation (EXUPair (run initial inputs (t + 1))).1)
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2))) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      v16457 (run initial inputs (t + 2)) (inputs (t + 2)) + 4 := by
  have pcs := committed_operand_pc_from_task10 _ _ _ currentReset commit pc
  have extended : extendOperandPC (EXUPair (run initial inputs (t + 1))).2 =
      (EXUPair (run initial inputs (t + 1))).2.signExtend 64 := by
    exact sign_extend_replication _ 25
  change extendOperandPC (EXUPair (run initial inputs (t + 1))).2 =
    v16457 (run initial inputs (t + 2)) (inputs (t + 2)) at pcs
  rw [extended] at pcs
  exact (jump_link_writeback_run initial inputs reset t operation commit unit matched).trans
    (congrArg (fun address : BitVec 64 => address + 4) pcs)
#print axioms jump_writeback_reference_pc_plus_four_run
end NutShellProofs
