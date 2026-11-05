import Proofs.RegisterExecution
import Proofs.JumpImmediate
import Proofs.MaskFacts
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
private theorem reg_jal_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 127 = 111) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 127 111 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_jal_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 127 = 111) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 127 111 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_jal_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 127 = 111) : exec_v7311 instruction pc rs1 rs2 = 1 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 1
  have yes : instruction &&& 127 = 111 :=
    mask_refines instruction 127 111 127 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_jal (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 127 = 111) :
    decodedExecution instruction pc rs1 rs2 = (pc + immediateJ instruction) := by
  simp only [decodedExecution, exec_v22, exec_v4, exec_v512, exec_v725, reg_jal_exec_v7303 instruction pc rs1 rs2 known, reg_jal_exec_v7307 instruction pc rs1 rs2 known, reg_jal_exec_v7311 instruction pc rs1 rs2 known, exec_v7521, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v7988, exec_v7989, exec_v7990, exec_v7991, exec_v7992, exec_v7993, exec_v7994, exec_v7995, exec_v7996, exec_v7997, exec_v7998, exec_v7999, exec_v8000, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
  rw [jump_middle_bits, jump_sign_replicate]
  rfl
#print axioms decoded_execution_jal
theorem writeback_execution_jal (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = (s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc + immediateJ s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) :=
  aligned.trans (decoded_execution_jal _ _ _ _ known)
#print axioms writeback_execution_jal
end RiscvMiniProofs
