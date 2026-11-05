import Proofs.ReferenceAddi
import Proofs.RegisterALUDecode
namespace NutShellProofs
open nNutCore

theorem register_alu_match_low32 (operation : RegisterALUOp) (instr : BitVec 64)
    (matched : IsRegisterALU operation instr) :
    BitVec.extractLsb' 0 32 instr &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32 := by
  have low := congrArg (BitVec.extractLsb' 0 32) matched
  cases operation <;> simpa only [BitVec.extractLsb'_and] using low

theorem register_alu_not_lui (operation : RegisterALUOp) (instr : BitVec 64)
    (matched : IsRegisterALU operation instr) :
    BitVec.extractLsb' 0 7 instr ≠ 55 := by
  have opcode := opcode_of_mask instr operation.mask operation.encoding (by cases operation <;> decide) matched.symm
  rw [opcode]
  cases operation <;> decide

theorem reference_register_alu_uses_rs1 (s : State) (i : Inputs) (operation : RegisterALUOp)
    (commit : v9 s i = 1)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    referenceUsesRs1 s i = true := by
  cases operation with
  | add =>
    apply reference_uses_rs1_of_register_add_match s i commit
    simp [v14989, v14987, v14988, v14576]
    exact matched.symm
  | sub =>
    apply reference_uses_rs1_of_register_sub_match s i commit
    simp [v14925, v14923, v14924, v14576]
    exact matched.symm
  | slt =>
    apply reference_uses_rs1_of_register_slt_match s i commit
    simp [v14981, v14979, v14980, v14576]
    exact matched.symm
  | sltu =>
    apply reference_uses_rs1_of_register_sltu_match s i commit
    simp [v14973, v14971, v14972, v14576]
    exact matched.symm
  | xor =>
    apply reference_uses_rs1_of_register_xor_match s i commit
    simp [v14949, v14947, v14948, v14576]
    exact matched.symm
  | or =>
    apply reference_uses_rs1_of_register_or_match s i commit
    simp [v14957, v14955, v14956, v14576]
    exact matched.symm
  | and =>
    apply reference_uses_rs1_of_register_and_match s i commit
    simp [v14965, v14963, v14964, v14576]
    exact matched.symm
  | sll =>
    apply reference_uses_rs1_of_register_sll_match s i commit
    simp [v14781, v14779, v14780, v14576]
    exact matched.symm
  | srl =>
    apply reference_uses_rs1_of_register_srl_match s i commit
    simp [v14773, v14771, v14772, v14576]
    exact matched.symm
  | sra =>
    apply reference_uses_rs1_of_register_sra_match s i commit
    simp [v14765, v14763, v14764, v14576]
    exact matched.symm

theorem committed_reference_register_alu_uses_rs1 (s : State) (i next : Inputs)
    (operation : RegisterALUOp) (commit : v9 (step s i) next = 1)
    (matched : IsRegisterALU operation s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    referenceUsesRs1 (step s i) next = true := by
  apply reference_register_alu_uses_rs1 _ _ operation commit
  rw [committed_reference_instruction s i next commit]
  exact register_alu_match_low32 operation _ matched
#print axioms committed_reference_register_alu_uses_rs1

theorem reference_register_alu_uses_rs2 (s : State) (i : Inputs) (operation : RegisterALUOp)
    (commit : v9 s i = 1)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    referenceUsesRs2 s i = true := by
  cases operation with
  | add =>
    apply reference_uses_rs2_of_register_add_match s i commit
    simp [v14989, v14987, v14988, v14576]
    exact matched.symm
  | sub =>
    apply reference_uses_rs2_of_register_sub_match s i commit
    simp [v14925, v14923, v14924, v14576]
    exact matched.symm
  | slt =>
    apply reference_uses_rs2_of_register_slt_match s i commit
    simp [v14981, v14979, v14980, v14576]
    exact matched.symm
  | sltu =>
    apply reference_uses_rs2_of_register_sltu_match s i commit
    simp [v14973, v14971, v14972, v14576]
    exact matched.symm
  | xor =>
    apply reference_uses_rs2_of_register_xor_match s i commit
    simp [v14949, v14947, v14948, v14576]
    exact matched.symm
  | or =>
    apply reference_uses_rs2_of_register_or_match s i commit
    simp [v14957, v14955, v14956, v14576]
    exact matched.symm
  | and =>
    apply reference_uses_rs2_of_register_and_match s i commit
    simp [v14965, v14963, v14964, v14576]
    exact matched.symm
  | sll =>
    apply reference_uses_rs2_of_register_sll_match s i commit
    simp [v14781, v14779, v14780, v14576]
    exact matched.symm
  | srl =>
    apply reference_uses_rs2_of_register_srl_match s i commit
    simp [v14773, v14771, v14772, v14576]
    exact matched.symm
  | sra =>
    apply reference_uses_rs2_of_register_sra_match s i commit
    simp [v14765, v14763, v14764, v14576]
    exact matched.symm

theorem committed_reference_register_alu_uses_rs2 (s : State) (i next : Inputs)
    (operation : RegisterALUOp) (commit : v9 (step s i) next = 1)
    (matched : IsRegisterALU operation s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    referenceUsesRs2 (step s i) next = true := by
  apply reference_register_alu_uses_rs2 _ _ operation commit
  rw [committed_reference_instruction s i next commit]
  exact register_alu_match_low32 operation _ matched
#print axioms committed_reference_register_alu_uses_rs2

end NutShellProofs
