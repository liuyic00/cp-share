import Proofs.ReferenceAddi
import Proofs.BranchRegisterStep
namespace NutShellProofs
open nNutCore

theorem branch_not_lui (operation : BranchOp) (instr : BitVec 64)
    (matched : IsBranch operation instr) :
    BitVec.extractLsb' 0 7 instr ≠ 55 := by
  have opcode := opcode_of_mask instr operation.mask operation.encoding (by cases operation <;> decide) matched.symm
  rw [opcode]
  cases operation <;> decide

theorem reference_branch_uses_rs1 (s : State) (i : Inputs) (operation : BranchOp)
    (commit : v9 s i = 1)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    referenceUsesRs1 s i = true := by
  cases operation with
  | beq =>
    apply reference_uses_rs1_of_branch_beq_match s i commit
    simp [v15227, v15224, v15226, v15225]
    exact matched.symm
  | bne =>
    apply reference_uses_rs1_of_branch_bne_match s i commit
    simp [v15220, v15217, v15219, v15218]
    exact matched.symm
  | blt =>
    apply reference_uses_rs1_of_branch_blt_match s i commit
    simp [v15213, v15210, v15212, v15211]
    exact matched.symm
  | bge =>
    apply reference_uses_rs1_of_branch_bge_match s i commit
    simp [v15199, v15196, v15198, v15197]
    exact matched.symm
  | bltu =>
    apply reference_uses_rs1_of_branch_bltu_match s i commit
    simp [v15206, v15203, v15205, v15204]
    exact matched.symm
  | bgeu =>
    apply reference_uses_rs1_of_branch_bgeu_match s i commit
    simp [v15192, v15189, v15191, v15190]
    exact matched.symm
theorem committed_reference_branch_uses_rs1 (s : State) (i next : Inputs)
    (operation : BranchOp) (commit : v9 (step s i) next = 1)
    (matched : IsBranch operation s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    referenceUsesRs1 (step s i) next = true := by
  apply reference_branch_uses_rs1 _ _ operation commit
  rw [committed_reference_instruction s i next commit]
  exact branch_match_low32 operation _ matched
#print axioms committed_reference_branch_uses_rs1
theorem reference_branch_uses_rs2 (s : State) (i : Inputs) (operation : BranchOp)
    (commit : v9 s i = 1)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    referenceUsesRs2 s i = true := by
  cases operation with
  | beq =>
    apply reference_uses_rs2_of_branch_beq_match s i commit
    simp [v15227, v15224, v15226, v15225]
    exact matched.symm
  | bne =>
    apply reference_uses_rs2_of_branch_bne_match s i commit
    simp [v15220, v15217, v15219, v15218]
    exact matched.symm
  | blt =>
    apply reference_uses_rs2_of_branch_blt_match s i commit
    simp [v15213, v15210, v15212, v15211]
    exact matched.symm
  | bge =>
    apply reference_uses_rs2_of_branch_bge_match s i commit
    simp [v15199, v15196, v15198, v15197]
    exact matched.symm
  | bltu =>
    apply reference_uses_rs2_of_branch_bltu_match s i commit
    simp [v15206, v15203, v15205, v15204]
    exact matched.symm
  | bgeu =>
    apply reference_uses_rs2_of_branch_bgeu_match s i commit
    simp [v15192, v15189, v15191, v15190]
    exact matched.symm
theorem committed_reference_branch_uses_rs2 (s : State) (i next : Inputs)
    (operation : BranchOp) (commit : v9 (step s i) next = 1)
    (matched : IsBranch operation s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    referenceUsesRs2 (step s i) next = true := by
  apply reference_branch_uses_rs2 _ _ operation commit
  rw [committed_reference_instruction s i next commit]
  exact branch_match_low32 operation _ matched
#print axioms committed_reference_branch_uses_rs2
end NutShellProofs
