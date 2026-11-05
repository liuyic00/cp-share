import Proofs.ReferenceAddi
import Proofs.ImmediateDecode
namespace NutShellProofs
open nNutCore

theorem immediate_match_low32 (operation : ImmediateALUOp) (instr : BitVec 64)
    (matched : IsImmediateALU operation instr) :
    BitVec.extractLsb' 0 32 instr &&& BitVec.ofNat 32 28799 = operation.encoding.setWidth 32 := by
  have low := congrArg (BitVec.extractLsb' 0 32) matched
  cases operation <;> simpa only [BitVec.extractLsb'_and] using low

theorem immediate_not_lui (operation : ImmediateALUOp) (instr : BitVec 64)
    (matched : IsImmediateALU operation instr) :
    BitVec.extractLsb' 0 7 instr ≠ 55 := by
  have opcode := opcode_of_mask instr (BitVec.ofNat 64 28799) operation.encoding (by decide) matched.symm
  rw [opcode]
  cases operation <;> decide

theorem reference_immediate_uses_rs1 (s : State) (i : Inputs) (operation : ImmediateALUOp)
    (commit : v9 s i = 1)
    (matched : v14575 s i &&& BitVec.ofNat 32 28799 = operation.encoding.setWidth 32) :
    referenceUsesRs1 s i = true := by
  cases operation with
  | add =>
    apply reference_uses_rs1_of_addi_match s i commit
    simp [ImmediateALUOp.encoding, v15071, v15068, v15070, v15069, matched, ↓reduceIte]
  | slt =>
    apply reference_uses_rs1_of_slti_match s i commit
    simp [ImmediateALUOp.encoding, v15063, v15060, v15062, v15061, matched, ↓reduceIte]
  | sltu =>
    apply reference_uses_rs1_of_sltiu_match s i commit
    simp [ImmediateALUOp.encoding, v15055, v15052, v15054, v15053, matched, ↓reduceIte]
  | xor =>
    apply reference_uses_rs1_of_xori_match s i commit
    simp [ImmediateALUOp.encoding, v15031, v15028, v15030, v15029, matched, ↓reduceIte]
  | or =>
    apply reference_uses_rs1_of_ori_match s i commit
    simp [ImmediateALUOp.encoding, v15039, v15036, v15038, v15037, matched, ↓reduceIte]
  | and =>
    apply reference_uses_rs1_of_andi_match s i commit
    simp [ImmediateALUOp.encoding, v15047, v15044, v15046, v15045, matched, ↓reduceIte]

theorem committed_reference_immediate_uses_rs1 (s : State) (i next : Inputs)
    (operation : ImmediateALUOp) (commit : v9 (step s i) next = 1)
    (matched : IsImmediateALU operation s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    referenceUsesRs1 (step s i) next = true := by
  apply reference_immediate_uses_rs1 _ _ operation commit
  rw [committed_reference_instruction s i next commit]
  exact immediate_match_low32 operation _ matched

#print axioms committed_reference_immediate_uses_rs1
end NutShellProofs
