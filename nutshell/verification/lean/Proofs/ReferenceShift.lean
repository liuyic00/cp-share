import Proofs.ReferenceAddi
import Proofs.ShiftDecode
namespace NutShellProofs
open nNutCore

theorem shift_match_low32 (operation : ShiftImmediateOp) (instr : BitVec 64)
    (matched : IsShiftImmediate operation instr) :
    BitVec.extractLsb' 0 32 instr &&& BitVec.ofNat 32 4227887231 = operation.encoding.setWidth 32 := by
  have low := congrArg (BitVec.extractLsb' 0 32) matched
  cases operation <;> simpa only [BitVec.extractLsb'_and] using low

theorem shift_not_lui (operation : ShiftImmediateOp) (instr : BitVec 64)
    (matched : IsShiftImmediate operation instr) :
    BitVec.extractLsb' 0 7 instr ≠ 55 := by
  have opcode := opcode_of_mask instr (BitVec.ofNat 64 4227887231) operation.encoding (by decide) matched.symm
  rw [opcode]
  cases operation <;> decide

theorem reference_shift_uses_rs1 (s : State) (i : Inputs) (operation : ShiftImmediateOp)
    (commit : v9 s i = 1)
    (matched : v14575 s i &&& BitVec.ofNat 32 4227887231 = operation.encoding.setWidth 32) :
    referenceUsesRs1 s i = true := by
  cases operation with
  | sll =>
    apply reference_uses_rs1_of_slli64_match s i commit
    simp [ShiftImmediateOp.encoding, v14825, v14823, v14824, v14809, matched]
  | srl =>
    apply reference_uses_rs1_of_srli64_match s i commit
    simp [ShiftImmediateOp.encoding, v14818, v14816, v14817, v14809, matched]
  | sra =>
    apply reference_uses_rs1_of_srai64_match s i commit
    simp [ShiftImmediateOp.encoding, v14811, v14808, v14810, v14809, matched]

theorem committed_reference_shift_uses_rs1 (s : State) (i next : Inputs)
    (operation : ShiftImmediateOp) (commit : v9 (step s i) next = 1)
    (matched : IsShiftImmediate operation s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    referenceUsesRs1 (step s i) next = true := by
  apply reference_shift_uses_rs1 _ _ operation commit
  rw [committed_reference_instruction s i next commit]
  exact shift_match_low32 operation _ matched

#print axioms committed_reference_shift_uses_rs1
end NutShellProofs
