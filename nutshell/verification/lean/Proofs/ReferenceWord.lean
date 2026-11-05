import Proofs.ReferenceAddi
import Proofs.WordDecode
namespace NutShellProofs
open nNutCore

theorem word_match_low32 (operation : WordImmediateOp) (instr : BitVec 64)
    (matched : IsWordImmediate operation instr) :
    BitVec.extractLsb' 0 32 instr &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32 := by
  have low := congrArg (BitVec.extractLsb' 0 32) matched
  cases operation <;> simpa only [BitVec.extractLsb'_and] using low

theorem word_not_lui (operation : WordImmediateOp) (instr : BitVec 64)
    (matched : IsWordImmediate operation instr) :
    BitVec.extractLsb' 0 7 instr ≠ 55 := by
  have opcode := opcode_of_mask instr operation.mask operation.encoding (by cases operation <;> decide) matched.symm
  rw [opcode]
  cases operation <;> decide

theorem reference_word_uses_rs1 (s : State) (i : Inputs) (operation : WordImmediateOp)
    (commit : v9 s i = 1)
    (matched : v14575 s i &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32) :
    referenceUsesRs1 s i = true := by
  cases operation with
  | add =>
    apply reference_uses_rs1_of_addiw_match s i commit
    simp [WordImmediateOp.encoding, WordImmediateOp.mask, v14833, v14830, v14832, v14831, matched]
    exact matched.symm
  | sll =>
    apply reference_uses_rs1_of_slliw_match s i commit
    simp [WordImmediateOp.encoding, WordImmediateOp.mask, v14803, v14801, v14802, v14576, matched]
    exact matched.symm
  | srl =>
    apply reference_uses_rs1_of_srliw_match s i commit
    simp [WordImmediateOp.encoding, WordImmediateOp.mask, v14796, v14794, v14795, v14576, matched]
    exact matched.symm
  | sra =>
    apply reference_uses_rs1_of_sraiw_match s i commit
    simp [WordImmediateOp.encoding, WordImmediateOp.mask, v14789, v14787, v14788, v14576, matched]
    exact matched.symm

theorem committed_reference_word_uses_rs1 (s : State) (i next : Inputs)
    (operation : WordImmediateOp) (commit : v9 (step s i) next = 1)
    (matched : IsWordImmediate operation s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    referenceUsesRs1 (step s i) next = true := by
  apply reference_word_uses_rs1 _ _ operation commit
  rw [committed_reference_instruction s i next commit]
  exact word_match_low32 operation _ matched

#print axioms committed_reference_word_uses_rs1
end NutShellProofs
