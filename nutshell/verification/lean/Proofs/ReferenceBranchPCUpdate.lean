import Proofs.ReferenceBranchException
import Proofs.ReferencePCUpdate
namespace NutShellProofs
open nNutCore

theorem reference_branch_no_exception (s : State) (i : Inputs) (operation : BranchOp)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32)
    (aligned : referenceBranchCondition operation s i = 1 → referenceBranchAlignment operation s i = 1) :
    v23407 s i = 0 := by
  cases operation with
  | beq => exact reference_branch_beq_no_exception s i matched aligned
  | bne => exact reference_branch_bne_no_exception s i matched aligned
  | blt => exact reference_branch_blt_no_exception s i matched aligned
  | bge => exact reference_branch_bge_no_exception s i matched aligned
  | bltu => exact reference_branch_bltu_no_exception s i matched aligned
  | bgeu => exact reference_branch_bgeu_no_exception s i matched aligned

theorem reference_branch_pc_update (s : State) (i : Inputs) (operation : BranchOp)
    (reset : i.g0.nreset = 0) (commit : v9 s i = 1)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32)
    (aligned : referenceBranchCondition operation s i = 1 → referenceBranchAlignment operation s i = 1) :
    (step s i).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc =
      if referenceBranchCondition operation s i = 1 then referenceBranchTarget operation s i
      else v16457 s i + 4 := by
  have noException := reference_branch_no_exception s i operation matched aligned
  cases operation with
  | beq => exact reference_branch_beq_pc_update s i reset commit noException matched aligned
  | bne => exact reference_branch_bne_pc_update s i reset commit noException matched aligned
  | blt => exact reference_branch_blt_pc_update s i reset commit noException matched aligned
  | bge => exact reference_branch_bge_pc_update s i reset commit noException matched aligned
  | bltu => exact reference_branch_bltu_pc_update s i reset commit noException matched aligned
  | bgeu => exact reference_branch_bgeu_pc_update s i reset commit noException matched aligned

#print axioms reference_branch_no_exception
#print axioms reference_branch_pc_update
end NutShellProofs
