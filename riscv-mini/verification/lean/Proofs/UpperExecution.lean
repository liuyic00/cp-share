import Proofs.RegisterExecution
import Proofs.ImmediateFacts
import Proofs.MaskFacts
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
private theorem reg_lui_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 127 = 55) : exec_v7303 instruction pc rs1 rs2 = 1 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 1
  have yes : instruction &&& 127 = 55 :=
    mask_refines instruction 127 55 127 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_lui (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 127 = 55) :
    decodedExecution instruction pc rs1 rs2 = (immediateU instruction) := by
  simp [decodedExecution, aluSpec, immediateU, exec_v1810, exec_v200, exec_v22, exec_v4, exec_v512, reg_lui_exec_v7303 instruction pc rs1 rs2 known, exec_v7521, exec_v7784, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8002, exec_v8003, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034]
#print axioms decoded_execution_lui
theorem writeback_execution_lui (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = (immediateU s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) :=
  aligned.trans (decoded_execution_lui _ _ _ _ known)
#print axioms writeback_execution_lui
private theorem reg_auipc_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 127 = 23) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 127 23 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_auipc_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 127 = 23) : exec_v7307 instruction pc rs1 rs2 = 1 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 1
  have yes : instruction &&& 127 = 23 :=
    mask_refines instruction 127 23 127 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_auipc (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 127 = 23) :
    decodedExecution instruction pc rs1 rs2 = (pc + immediateU instruction) := by
  simp [decodedExecution, aluSpec, immediateU, exec_v1810, exec_v200, exec_v22, exec_v4, exec_v512, exec_v725, reg_auipc_exec_v7303 instruction pc rs1 rs2 known, reg_auipc_exec_v7307 instruction pc rs1 rs2 known, exec_v7521, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8002, exec_v8003, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034]
#print axioms decoded_execution_auipc
theorem writeback_execution_auipc (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = (s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc + immediateU s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) :=
  aligned.trans (decoded_execution_auipc _ _ _ _ known)
#print axioms writeback_execution_auipc
end RiscvMiniProofs
