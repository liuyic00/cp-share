import Proofs.ReferenceBranchOperands
import Proofs.BranchConditions
import Proofs.AluOperandCorrespondence
namespace NutShellProofs
open nNutCore

theorem branch_condition_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    v12179 (run initial inputs (t + 1)) (inputs (t + 1)) =
      if operation.condition (v15632 (run initial inputs (t + 2)) (inputs (t + 2)))
        (v15394 (run initial inputs (t + 2)) (inputs (t + 2))) then 1 else 0 := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨_, kind1, kind2, _, _⟩ :=
    (branch_decode_run initial inputs reset t).2 valid operation matched unit
  have used1 := committed_reference_branch_uses_rs1 _ _ _ operation commit matched
  have used2 := committed_reference_branch_uses_rs2 _ _ _ operation commit matched
  obtain ⟨source1, source2⟩ := execute_register_operands_run initial inputs reset t
    commit kind1 kind2 aligned used1 used2 (branch_not_lui operation _ matched)
  have result := branch_condition_run initial inputs reset t operation valid unit matched
  simpa only [source1, source2] using result

#print axioms branch_condition_reference_run
end NutShellProofs
