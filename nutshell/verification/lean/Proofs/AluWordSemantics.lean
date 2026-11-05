import Proofs.AluWordResults
namespace NutShellProofs
open nNutCore

theorem alu_result_sllw_word (s : State) (i : Inputs) (op : v28 s i = 33) :
    v25095 s i = ((BitVec.extractLsb' 0 32 (v12148 s i)) <<<
      (BitVec.extractLsb' 0 5 (v12150 s i)).toNat).signExtend 64 := by
  rw [alu_result_sllw s i op]
  simp only [BitVec.shiftLeft_eq]
  rw [low_shiftLeft _ _ (by decide)]

theorem alu_result_srlw_word (s : State) (i : Inputs) (op : v28 s i = 37) :
    v25095 s i = ((BitVec.extractLsb' 0 32 (v12148 s i)) >>>
      (BitVec.extractLsb' 0 5 (v12150 s i)).toNat).signExtend 64 := by
  rw [alu_result_srlw s i op]
  simp only [BitVec.ushiftRight_eq]
  rw [word_logical_shift]

theorem alu_result_sraw_word (s : State) (i : Inputs) (op : v28 s i = 45) :
    v25095 s i = ((BitVec.extractLsb' 0 32 (v12148 s i)).sshiftRight
      (BitVec.extractLsb' 0 5 (v12150 s i)).toNat).signExtend 64 := by
  rw [alu_result_sraw s i op, word_arithmetic_shift]

theorem writeback_alu_sllw_word (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0) (op : v28 s i = 33) :
    v11842 (step s i) next = ((BitVec.extractLsb' 0 32 (v12148 s i)) <<<
      (BitVec.extractLsb' 0 5 (v12150 s i)).toNat).signExtend 64 := by
  rw [writeback_capture_0 s i next commit unit]
  exact alu_result_sllw_word s i op

theorem writeback_alu_srlw_word (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0) (op : v28 s i = 37) :
    v11842 (step s i) next = ((BitVec.extractLsb' 0 32 (v12148 s i)) >>>
      (BitVec.extractLsb' 0 5 (v12150 s i)).toNat).signExtend 64 := by
  rw [writeback_capture_0 s i next commit unit]
  exact alu_result_srlw_word s i op

theorem writeback_alu_sraw_word (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0) (op : v28 s i = 45) :
    v11842 (step s i) next = ((BitVec.extractLsb' 0 32 (v12148 s i)).sshiftRight
      (BitVec.extractLsb' 0 5 (v12150 s i)).toNat).signExtend 64 := by
  rw [writeback_capture_0 s i next commit unit]
  exact alu_result_sraw_word s i op

#print axioms writeback_alu_sllw_word
#print axioms writeback_alu_srlw_word
#print axioms writeback_alu_sraw_word
end NutShellProofs
