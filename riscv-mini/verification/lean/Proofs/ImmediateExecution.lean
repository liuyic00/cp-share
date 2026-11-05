import Proofs.RegisterExecution
import Proofs.ImmediateFacts
import Proofs.MaskFacts
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
private theorem reg_addi_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 19 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 19 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 19 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 19 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 19 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 19 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 19 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 19 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 19 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 19 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : exec_v7343 instruction pc rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 28799 19 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_exec_v7347 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : exec_v7347 instruction pc rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 28799 19 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_exec_v7351 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : exec_v7351 instruction pc rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 28799 19 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_exec_v7355 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : exec_v7355 instruction pc rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 28799 19 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_exec_v7359 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : exec_v7359 instruction pc rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 28799 19 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_exec_v7363 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : exec_v7363 instruction pc rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 28799 19 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_exec_v7367 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : exec_v7367 instruction pc rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 28799 19 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_exec_v7371 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : exec_v7371 instruction pc rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 28799 19 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_exec_v7375 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : exec_v7375 instruction pc rs1 rs2 = 1 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 19 :=
    mask_refines instruction 28799 19 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_addi (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) :
    decodedExecution instruction pc rs1 rs2 = (rs1 + immediateI instruction) := by
  simp only [decodedExecution, exec_v200, exec_v22, exec_v26, exec_v29, exec_v4, exec_v512, exec_v716, exec_v725, reg_addi_exec_v7303 instruction pc rs1 rs2 known, reg_addi_exec_v7307 instruction pc rs1 rs2 known, reg_addi_exec_v7311 instruction pc rs1 rs2 known, reg_addi_exec_v7315 instruction pc rs1 rs2 known, reg_addi_exec_v7319 instruction pc rs1 rs2 known, reg_addi_exec_v7323 instruction pc rs1 rs2 known, reg_addi_exec_v7327 instruction pc rs1 rs2 known, reg_addi_exec_v7331 instruction pc rs1 rs2 known, reg_addi_exec_v7335 instruction pc rs1 rs2 known, reg_addi_exec_v7339 instruction pc rs1 rs2 known, reg_addi_exec_v7343 instruction pc rs1 rs2 known, reg_addi_exec_v7347 instruction pc rs1 rs2 known, reg_addi_exec_v7351 instruction pc rs1 rs2 known, reg_addi_exec_v7355 instruction pc rs1 rs2 known, reg_addi_exec_v7359 instruction pc rs1 rs2 known, reg_addi_exec_v7363 instruction pc rs1 rs2 known, reg_addi_exec_v7367 instruction pc rs1 rs2 known, reg_addi_exec_v7371 instruction pc rs1 rs2 known, reg_addi_exec_v7375 instruction pc rs1 rs2 known, exec_v7521, exec_v7819, exec_v7820, exec_v7821, exec_v7822, exec_v7823, exec_v7824, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7866, exec_v7867, exec_v7868, exec_v7869, exec_v7870, exec_v7871, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7910, exec_v7911, exec_v7912, exec_v7913, exec_v7914, exec_v7915, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7958, exec_v7959, exec_v7960, exec_v7961, exec_v7962, exec_v7963, exec_v7964, exec_v7965, exec_v7966, exec_v7967, exec_v7968, exec_v7969, exec_v7970, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8013, exec_v8017, exec_v8018, exec_v8021, exec_v8022, exec_v8023, exec_v8024, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
  rw [dut_immediate_form instruction]
  simp [aluSpec, immediateI_low5]
#print axioms decoded_execution_addi
theorem writeback_execution_addi (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = ((writebackRs1 s) + immediateI s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) :=
  aligned.trans (decoded_execution_addi _ _ _ _ known)
#print axioms writeback_execution_addi
private theorem reg_slti_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 8211 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 8211 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 8211 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 8211 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 8211 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 8211 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 8211 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 8211 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 8211 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 8211 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : exec_v7343 instruction pc rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 28799 8211 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_exec_v7347 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : exec_v7347 instruction pc rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 28799 8211 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_exec_v7351 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : exec_v7351 instruction pc rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 28799 8211 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_exec_v7355 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : exec_v7355 instruction pc rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 28799 8211 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_exec_v7359 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : exec_v7359 instruction pc rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 28799 8211 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_exec_v7363 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : exec_v7363 instruction pc rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 28799 8211 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_exec_v7367 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : exec_v7367 instruction pc rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 28799 8211 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_exec_v7371 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : exec_v7371 instruction pc rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 28799 8211 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_exec_v7375 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : exec_v7375 instruction pc rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 28799 8211 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_exec_v7379 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : exec_v7379 instruction pc rs1 rs2 = 1 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 8211 :=
    mask_refines instruction 28799 8211 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_slti (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) :
    decodedExecution instruction pc rs1 rs2 = (if rs1.toInt < (immediateI instruction).toInt then 1 else 0) := by
  simp only [decodedExecution, exec_v200, exec_v22, exec_v26, exec_v29, exec_v4, exec_v512, exec_v716, reg_slti_exec_v7303 instruction pc rs1 rs2 known, reg_slti_exec_v7307 instruction pc rs1 rs2 known, reg_slti_exec_v7311 instruction pc rs1 rs2 known, reg_slti_exec_v7315 instruction pc rs1 rs2 known, reg_slti_exec_v7319 instruction pc rs1 rs2 known, reg_slti_exec_v7323 instruction pc rs1 rs2 known, reg_slti_exec_v7327 instruction pc rs1 rs2 known, reg_slti_exec_v7331 instruction pc rs1 rs2 known, reg_slti_exec_v7335 instruction pc rs1 rs2 known, reg_slti_exec_v7339 instruction pc rs1 rs2 known, reg_slti_exec_v7343 instruction pc rs1 rs2 known, reg_slti_exec_v7347 instruction pc rs1 rs2 known, reg_slti_exec_v7351 instruction pc rs1 rs2 known, reg_slti_exec_v7355 instruction pc rs1 rs2 known, reg_slti_exec_v7359 instruction pc rs1 rs2 known, reg_slti_exec_v7363 instruction pc rs1 rs2 known, reg_slti_exec_v7367 instruction pc rs1 rs2 known, reg_slti_exec_v7371 instruction pc rs1 rs2 known, reg_slti_exec_v7375 instruction pc rs1 rs2 known, reg_slti_exec_v7379 instruction pc rs1 rs2 known, exec_v7521, exec_v7785, exec_v7818, exec_v7819, exec_v7820, exec_v7821, exec_v7822, exec_v7823, exec_v7824, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7865, exec_v7866, exec_v7867, exec_v7868, exec_v7869, exec_v7870, exec_v7871, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7909, exec_v7910, exec_v7911, exec_v7912, exec_v7913, exec_v7914, exec_v7915, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7957, exec_v7958, exec_v7959, exec_v7960, exec_v7961, exec_v7962, exec_v7963, exec_v7964, exec_v7965, exec_v7966, exec_v7967, exec_v7968, exec_v7969, exec_v7970, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8013, exec_v8017, exec_v8018, exec_v8021, exec_v8022, exec_v8023, exec_v8024, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
  rw [dut_immediate_form instruction]
  simp [aluSpec, immediateI_low5]
#print axioms decoded_execution_slti
theorem writeback_execution_slti (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = (if (writebackRs1 s).toInt < (immediateI s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst).toInt then 1 else 0) :=
  aligned.trans (decoded_execution_slti _ _ _ _ known)
#print axioms writeback_execution_slti
private theorem reg_sltiu_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 12307 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 12307 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 12307 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 12307 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 12307 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 12307 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 12307 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 12307 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 12307 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 12307 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : exec_v7343 instruction pc rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 28799 12307 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_exec_v7347 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : exec_v7347 instruction pc rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 28799 12307 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_exec_v7351 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : exec_v7351 instruction pc rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 28799 12307 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_exec_v7355 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : exec_v7355 instruction pc rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 28799 12307 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_exec_v7359 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : exec_v7359 instruction pc rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 28799 12307 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_exec_v7363 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : exec_v7363 instruction pc rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 28799 12307 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_exec_v7367 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : exec_v7367 instruction pc rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 28799 12307 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_exec_v7371 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : exec_v7371 instruction pc rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 28799 12307 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_exec_v7375 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : exec_v7375 instruction pc rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 28799 12307 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_exec_v7379 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : exec_v7379 instruction pc rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 28799 12307 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_exec_v7383 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : exec_v7383 instruction pc rs1 rs2 = 1 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 12307 :=
    mask_refines instruction 28799 12307 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_sltiu (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) :
    decodedExecution instruction pc rs1 rs2 = (if rs1.toNat < (immediateI instruction).toNat then 1 else 0) := by
  simp only [decodedExecution, exec_v200, exec_v22, exec_v26, exec_v29, exec_v4, exec_v512, exec_v716, reg_sltiu_exec_v7303 instruction pc rs1 rs2 known, reg_sltiu_exec_v7307 instruction pc rs1 rs2 known, reg_sltiu_exec_v7311 instruction pc rs1 rs2 known, reg_sltiu_exec_v7315 instruction pc rs1 rs2 known, reg_sltiu_exec_v7319 instruction pc rs1 rs2 known, reg_sltiu_exec_v7323 instruction pc rs1 rs2 known, reg_sltiu_exec_v7327 instruction pc rs1 rs2 known, reg_sltiu_exec_v7331 instruction pc rs1 rs2 known, reg_sltiu_exec_v7335 instruction pc rs1 rs2 known, reg_sltiu_exec_v7339 instruction pc rs1 rs2 known, reg_sltiu_exec_v7343 instruction pc rs1 rs2 known, reg_sltiu_exec_v7347 instruction pc rs1 rs2 known, reg_sltiu_exec_v7351 instruction pc rs1 rs2 known, reg_sltiu_exec_v7355 instruction pc rs1 rs2 known, reg_sltiu_exec_v7359 instruction pc rs1 rs2 known, reg_sltiu_exec_v7363 instruction pc rs1 rs2 known, reg_sltiu_exec_v7367 instruction pc rs1 rs2 known, reg_sltiu_exec_v7371 instruction pc rs1 rs2 known, reg_sltiu_exec_v7375 instruction pc rs1 rs2 known, reg_sltiu_exec_v7379 instruction pc rs1 rs2 known, reg_sltiu_exec_v7383 instruction pc rs1 rs2 known, exec_v7521, exec_v7786, exec_v7817, exec_v7818, exec_v7819, exec_v7820, exec_v7821, exec_v7822, exec_v7823, exec_v7824, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7864, exec_v7865, exec_v7866, exec_v7867, exec_v7868, exec_v7869, exec_v7870, exec_v7871, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7908, exec_v7909, exec_v7910, exec_v7911, exec_v7912, exec_v7913, exec_v7914, exec_v7915, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7956, exec_v7957, exec_v7958, exec_v7959, exec_v7960, exec_v7961, exec_v7962, exec_v7963, exec_v7964, exec_v7965, exec_v7966, exec_v7967, exec_v7968, exec_v7969, exec_v7970, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8013, exec_v8017, exec_v8018, exec_v8021, exec_v8022, exec_v8023, exec_v8024, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
  rw [dut_immediate_form instruction]
  simp [aluSpec, immediateI_low5]
#print axioms decoded_execution_sltiu
theorem writeback_execution_sltiu (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = (if (writebackRs1 s).toNat < (immediateI s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst).toNat then 1 else 0) :=
  aligned.trans (decoded_execution_sltiu _ _ _ _ known)
#print axioms writeback_execution_sltiu
private theorem reg_xori_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 16403 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 16403 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 16403 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 16403 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 16403 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 16403 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 16403 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 16403 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 16403 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 16403 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : exec_v7343 instruction pc rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 28799 16403 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_exec_v7347 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : exec_v7347 instruction pc rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 28799 16403 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_exec_v7351 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : exec_v7351 instruction pc rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 28799 16403 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_exec_v7355 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : exec_v7355 instruction pc rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 28799 16403 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_exec_v7359 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : exec_v7359 instruction pc rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 28799 16403 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_exec_v7363 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : exec_v7363 instruction pc rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 28799 16403 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_exec_v7367 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : exec_v7367 instruction pc rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 28799 16403 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_exec_v7371 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : exec_v7371 instruction pc rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 28799 16403 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_exec_v7375 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : exec_v7375 instruction pc rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 28799 16403 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_exec_v7379 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : exec_v7379 instruction pc rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 28799 16403 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_exec_v7383 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : exec_v7383 instruction pc rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 28799 16403 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_exec_v7387 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : exec_v7387 instruction pc rs1 rs2 = 1 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 16403 :=
    mask_refines instruction 28799 16403 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_xori (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) :
    decodedExecution instruction pc rs1 rs2 = (rs1 ^^^ immediateI instruction) := by
  simp only [decodedExecution, exec_v200, exec_v22, exec_v26, exec_v29, exec_v4, exec_v512, exec_v716, reg_xori_exec_v7303 instruction pc rs1 rs2 known, reg_xori_exec_v7307 instruction pc rs1 rs2 known, reg_xori_exec_v7311 instruction pc rs1 rs2 known, reg_xori_exec_v7315 instruction pc rs1 rs2 known, reg_xori_exec_v7319 instruction pc rs1 rs2 known, reg_xori_exec_v7323 instruction pc rs1 rs2 known, reg_xori_exec_v7327 instruction pc rs1 rs2 known, reg_xori_exec_v7331 instruction pc rs1 rs2 known, reg_xori_exec_v7335 instruction pc rs1 rs2 known, reg_xori_exec_v7339 instruction pc rs1 rs2 known, reg_xori_exec_v7343 instruction pc rs1 rs2 known, reg_xori_exec_v7347 instruction pc rs1 rs2 known, reg_xori_exec_v7351 instruction pc rs1 rs2 known, reg_xori_exec_v7355 instruction pc rs1 rs2 known, reg_xori_exec_v7359 instruction pc rs1 rs2 known, reg_xori_exec_v7363 instruction pc rs1 rs2 known, reg_xori_exec_v7367 instruction pc rs1 rs2 known, reg_xori_exec_v7371 instruction pc rs1 rs2 known, reg_xori_exec_v7375 instruction pc rs1 rs2 known, reg_xori_exec_v7379 instruction pc rs1 rs2 known, reg_xori_exec_v7383 instruction pc rs1 rs2 known, reg_xori_exec_v7387 instruction pc rs1 rs2 known, exec_v7521, exec_v7787, exec_v7816, exec_v7817, exec_v7818, exec_v7819, exec_v7820, exec_v7821, exec_v7822, exec_v7823, exec_v7824, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7863, exec_v7864, exec_v7865, exec_v7866, exec_v7867, exec_v7868, exec_v7869, exec_v7870, exec_v7871, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7907, exec_v7908, exec_v7909, exec_v7910, exec_v7911, exec_v7912, exec_v7913, exec_v7914, exec_v7915, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7955, exec_v7956, exec_v7957, exec_v7958, exec_v7959, exec_v7960, exec_v7961, exec_v7962, exec_v7963, exec_v7964, exec_v7965, exec_v7966, exec_v7967, exec_v7968, exec_v7969, exec_v7970, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8013, exec_v8017, exec_v8018, exec_v8021, exec_v8022, exec_v8023, exec_v8024, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
  rw [dut_immediate_form instruction]
  simp [aluSpec, immediateI_low5]
#print axioms decoded_execution_xori
theorem writeback_execution_xori (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = ((writebackRs1 s) ^^^ immediateI s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) :=
  aligned.trans (decoded_execution_xori _ _ _ _ known)
#print axioms writeback_execution_xori
private theorem reg_ori_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 24595 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 24595 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 24595 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 24595 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 24595 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 24595 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 24595 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 24595 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 24595 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 24595 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : exec_v7343 instruction pc rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 28799 24595 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_exec_v7347 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : exec_v7347 instruction pc rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 28799 24595 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_exec_v7351 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : exec_v7351 instruction pc rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 28799 24595 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_exec_v7355 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : exec_v7355 instruction pc rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 28799 24595 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_exec_v7359 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : exec_v7359 instruction pc rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 28799 24595 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_exec_v7363 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : exec_v7363 instruction pc rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 28799 24595 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_exec_v7367 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : exec_v7367 instruction pc rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 28799 24595 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_exec_v7371 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : exec_v7371 instruction pc rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 28799 24595 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_exec_v7375 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : exec_v7375 instruction pc rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 28799 24595 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_exec_v7379 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : exec_v7379 instruction pc rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 28799 24595 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_exec_v7383 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : exec_v7383 instruction pc rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 28799 24595 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_exec_v7387 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : exec_v7387 instruction pc rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 28799 24595 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_exec_v7391 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : exec_v7391 instruction pc rs1 rs2 = 1 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 24595 :=
    mask_refines instruction 28799 24595 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_ori (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) :
    decodedExecution instruction pc rs1 rs2 = (rs1 ||| immediateI instruction) := by
  simp only [decodedExecution, exec_v200, exec_v22, exec_v26, exec_v29, exec_v4, exec_v512, exec_v716, reg_ori_exec_v7303 instruction pc rs1 rs2 known, reg_ori_exec_v7307 instruction pc rs1 rs2 known, reg_ori_exec_v7311 instruction pc rs1 rs2 known, reg_ori_exec_v7315 instruction pc rs1 rs2 known, reg_ori_exec_v7319 instruction pc rs1 rs2 known, reg_ori_exec_v7323 instruction pc rs1 rs2 known, reg_ori_exec_v7327 instruction pc rs1 rs2 known, reg_ori_exec_v7331 instruction pc rs1 rs2 known, reg_ori_exec_v7335 instruction pc rs1 rs2 known, reg_ori_exec_v7339 instruction pc rs1 rs2 known, reg_ori_exec_v7343 instruction pc rs1 rs2 known, reg_ori_exec_v7347 instruction pc rs1 rs2 known, reg_ori_exec_v7351 instruction pc rs1 rs2 known, reg_ori_exec_v7355 instruction pc rs1 rs2 known, reg_ori_exec_v7359 instruction pc rs1 rs2 known, reg_ori_exec_v7363 instruction pc rs1 rs2 known, reg_ori_exec_v7367 instruction pc rs1 rs2 known, reg_ori_exec_v7371 instruction pc rs1 rs2 known, reg_ori_exec_v7375 instruction pc rs1 rs2 known, reg_ori_exec_v7379 instruction pc rs1 rs2 known, reg_ori_exec_v7383 instruction pc rs1 rs2 known, reg_ori_exec_v7387 instruction pc rs1 rs2 known, reg_ori_exec_v7391 instruction pc rs1 rs2 known, exec_v7521, exec_v7788, exec_v7815, exec_v7816, exec_v7817, exec_v7818, exec_v7819, exec_v7820, exec_v7821, exec_v7822, exec_v7823, exec_v7824, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7862, exec_v7863, exec_v7864, exec_v7865, exec_v7866, exec_v7867, exec_v7868, exec_v7869, exec_v7870, exec_v7871, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7906, exec_v7907, exec_v7908, exec_v7909, exec_v7910, exec_v7911, exec_v7912, exec_v7913, exec_v7914, exec_v7915, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7954, exec_v7955, exec_v7956, exec_v7957, exec_v7958, exec_v7959, exec_v7960, exec_v7961, exec_v7962, exec_v7963, exec_v7964, exec_v7965, exec_v7966, exec_v7967, exec_v7968, exec_v7969, exec_v7970, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8013, exec_v8017, exec_v8018, exec_v8021, exec_v8022, exec_v8023, exec_v8024, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
  rw [dut_immediate_form instruction]
  simp [aluSpec, immediateI_low5]
#print axioms decoded_execution_ori
theorem writeback_execution_ori (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = ((writebackRs1 s) ||| immediateI s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) :=
  aligned.trans (decoded_execution_ori _ _ _ _ known)
#print axioms writeback_execution_ori
private theorem reg_andi_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 28691 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 28691 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 28691 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 28691 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 28691 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 28691 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 28691 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 28691 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 28691 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 28691 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7343 instruction pc rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 28799 28691 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_exec_v7347 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7347 instruction pc rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 28799 28691 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_exec_v7351 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7351 instruction pc rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 28799 28691 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_exec_v7355 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7355 instruction pc rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 28799 28691 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_exec_v7359 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7359 instruction pc rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 28799 28691 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_exec_v7363 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7363 instruction pc rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 28799 28691 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_exec_v7367 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7367 instruction pc rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 28799 28691 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_exec_v7371 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7371 instruction pc rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 28799 28691 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_exec_v7375 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7375 instruction pc rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 28799 28691 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_exec_v7379 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7379 instruction pc rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 28799 28691 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_exec_v7383 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7383 instruction pc rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 28799 28691 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_exec_v7387 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7387 instruction pc rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 28799 28691 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_exec_v7391 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7391 instruction pc rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 28799 28691 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_exec_v7395 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : exec_v7395 instruction pc rs1 rs2 = 1 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 28691 :=
    mask_refines instruction 28799 28691 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_andi (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) :
    decodedExecution instruction pc rs1 rs2 = (rs1 &&& immediateI instruction) := by
  simp only [decodedExecution, exec_v200, exec_v22, exec_v26, exec_v29, exec_v4, exec_v512, exec_v716, reg_andi_exec_v7303 instruction pc rs1 rs2 known, reg_andi_exec_v7307 instruction pc rs1 rs2 known, reg_andi_exec_v7311 instruction pc rs1 rs2 known, reg_andi_exec_v7315 instruction pc rs1 rs2 known, reg_andi_exec_v7319 instruction pc rs1 rs2 known, reg_andi_exec_v7323 instruction pc rs1 rs2 known, reg_andi_exec_v7327 instruction pc rs1 rs2 known, reg_andi_exec_v7331 instruction pc rs1 rs2 known, reg_andi_exec_v7335 instruction pc rs1 rs2 known, reg_andi_exec_v7339 instruction pc rs1 rs2 known, reg_andi_exec_v7343 instruction pc rs1 rs2 known, reg_andi_exec_v7347 instruction pc rs1 rs2 known, reg_andi_exec_v7351 instruction pc rs1 rs2 known, reg_andi_exec_v7355 instruction pc rs1 rs2 known, reg_andi_exec_v7359 instruction pc rs1 rs2 known, reg_andi_exec_v7363 instruction pc rs1 rs2 known, reg_andi_exec_v7367 instruction pc rs1 rs2 known, reg_andi_exec_v7371 instruction pc rs1 rs2 known, reg_andi_exec_v7375 instruction pc rs1 rs2 known, reg_andi_exec_v7379 instruction pc rs1 rs2 known, reg_andi_exec_v7383 instruction pc rs1 rs2 known, reg_andi_exec_v7387 instruction pc rs1 rs2 known, reg_andi_exec_v7391 instruction pc rs1 rs2 known, reg_andi_exec_v7395 instruction pc rs1 rs2 known, exec_v7521, exec_v7789, exec_v7814, exec_v7815, exec_v7816, exec_v7817, exec_v7818, exec_v7819, exec_v7820, exec_v7821, exec_v7822, exec_v7823, exec_v7824, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7861, exec_v7862, exec_v7863, exec_v7864, exec_v7865, exec_v7866, exec_v7867, exec_v7868, exec_v7869, exec_v7870, exec_v7871, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7905, exec_v7906, exec_v7907, exec_v7908, exec_v7909, exec_v7910, exec_v7911, exec_v7912, exec_v7913, exec_v7914, exec_v7915, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7953, exec_v7954, exec_v7955, exec_v7956, exec_v7957, exec_v7958, exec_v7959, exec_v7960, exec_v7961, exec_v7962, exec_v7963, exec_v7964, exec_v7965, exec_v7966, exec_v7967, exec_v7968, exec_v7969, exec_v7970, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8013, exec_v8017, exec_v8018, exec_v8021, exec_v8022, exec_v8023, exec_v8024, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
  rw [dut_immediate_form instruction]
  simp [aluSpec, immediateI_low5]
#print axioms decoded_execution_andi
theorem writeback_execution_andi (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = ((writebackRs1 s) &&& immediateI s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) :=
  aligned.trans (decoded_execution_andi _ _ _ _ known)
#print axioms writeback_execution_andi
private theorem reg_slli_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 4115 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 4115 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 4115 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 4115 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 4115 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 4115 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 4115 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 4115 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 4115 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 4115 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7343 instruction pc rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 4115 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7347 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7347 instruction pc rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 4115 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7351 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7351 instruction pc rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 4115 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7355 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7355 instruction pc rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 4115 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7359 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7359 instruction pc rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 4115 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7363 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7363 instruction pc rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 4115 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7367 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7367 instruction pc rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 4115 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7371 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7371 instruction pc rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 4115 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7375 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7375 instruction pc rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 4115 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7379 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7379 instruction pc rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 4115 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7383 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7383 instruction pc rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 4115 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7387 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7387 instruction pc rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 4115 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7391 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7391 instruction pc rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 4115 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7395 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7395 instruction pc rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 4115 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_exec_v7398 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : exec_v7398 instruction pc rs1 rs2 = 1 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 4115 :=
    mask_refines instruction 4261441663 4115 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_slli (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) :
    decodedExecution instruction pc rs1 rs2 = (rs1.shiftLeft (BitVec.extractLsb' 20 5 instruction).toNat) := by
  simp only [decodedExecution, exec_v200, exec_v22, exec_v26, exec_v29, exec_v4, exec_v512, exec_v716, reg_slli_exec_v7303 instruction pc rs1 rs2 known, reg_slli_exec_v7307 instruction pc rs1 rs2 known, reg_slli_exec_v7311 instruction pc rs1 rs2 known, reg_slli_exec_v7315 instruction pc rs1 rs2 known, reg_slli_exec_v7319 instruction pc rs1 rs2 known, reg_slli_exec_v7323 instruction pc rs1 rs2 known, reg_slli_exec_v7327 instruction pc rs1 rs2 known, reg_slli_exec_v7331 instruction pc rs1 rs2 known, reg_slli_exec_v7335 instruction pc rs1 rs2 known, reg_slli_exec_v7339 instruction pc rs1 rs2 known, reg_slli_exec_v7343 instruction pc rs1 rs2 known, reg_slli_exec_v7347 instruction pc rs1 rs2 known, reg_slli_exec_v7351 instruction pc rs1 rs2 known, reg_slli_exec_v7355 instruction pc rs1 rs2 known, reg_slli_exec_v7359 instruction pc rs1 rs2 known, reg_slli_exec_v7363 instruction pc rs1 rs2 known, reg_slli_exec_v7367 instruction pc rs1 rs2 known, reg_slli_exec_v7371 instruction pc rs1 rs2 known, reg_slli_exec_v7375 instruction pc rs1 rs2 known, reg_slli_exec_v7379 instruction pc rs1 rs2 known, reg_slli_exec_v7383 instruction pc rs1 rs2 known, reg_slli_exec_v7387 instruction pc rs1 rs2 known, reg_slli_exec_v7391 instruction pc rs1 rs2 known, reg_slli_exec_v7395 instruction pc rs1 rs2 known, reg_slli_exec_v7398 instruction pc rs1 rs2 known, exec_v7521, exec_v7790, exec_v7813, exec_v7814, exec_v7815, exec_v7816, exec_v7817, exec_v7818, exec_v7819, exec_v7820, exec_v7821, exec_v7822, exec_v7823, exec_v7824, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7860, exec_v7861, exec_v7862, exec_v7863, exec_v7864, exec_v7865, exec_v7866, exec_v7867, exec_v7868, exec_v7869, exec_v7870, exec_v7871, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7904, exec_v7905, exec_v7906, exec_v7907, exec_v7908, exec_v7909, exec_v7910, exec_v7911, exec_v7912, exec_v7913, exec_v7914, exec_v7915, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7952, exec_v7953, exec_v7954, exec_v7955, exec_v7956, exec_v7957, exec_v7958, exec_v7959, exec_v7960, exec_v7961, exec_v7962, exec_v7963, exec_v7964, exec_v7965, exec_v7966, exec_v7967, exec_v7968, exec_v7969, exec_v7970, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8013, exec_v8017, exec_v8018, exec_v8021, exec_v8022, exec_v8023, exec_v8024, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
  rw [dut_immediate_form instruction]
  simp [aluSpec, immediateI_low5]
#print axioms decoded_execution_slli
theorem writeback_execution_slli (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = ((writebackRs1 s).shiftLeft (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst).toNat) :=
  aligned.trans (decoded_execution_slli _ _ _ _ known)
#print axioms writeback_execution_slli
private theorem reg_srli_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 20499 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 20499 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 20499 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 20499 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 20499 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 20499 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 20499 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 20499 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 20499 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 20499 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7343 instruction pc rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 20499 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7347 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7347 instruction pc rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 20499 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7351 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7351 instruction pc rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 20499 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7355 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7355 instruction pc rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 20499 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7359 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7359 instruction pc rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 20499 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7363 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7363 instruction pc rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 20499 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7367 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7367 instruction pc rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 20499 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7371 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7371 instruction pc rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 20499 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7375 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7375 instruction pc rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 20499 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7379 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7379 instruction pc rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 20499 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7383 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7383 instruction pc rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 20499 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7387 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7387 instruction pc rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 20499 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7391 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7391 instruction pc rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 20499 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7395 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7395 instruction pc rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 20499 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7398 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7398 instruction pc rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 20499 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_exec_v7401 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : exec_v7401 instruction pc rs1 rs2 = 1 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 20499 :=
    mask_refines instruction 4261441663 20499 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_srli (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) :
    decodedExecution instruction pc rs1 rs2 = (rs1.ushiftRight (BitVec.extractLsb' 20 5 instruction).toNat) := by
  simp only [decodedExecution, exec_v200, exec_v22, exec_v26, exec_v29, exec_v4, exec_v512, exec_v716, reg_srli_exec_v7303 instruction pc rs1 rs2 known, reg_srli_exec_v7307 instruction pc rs1 rs2 known, reg_srli_exec_v7311 instruction pc rs1 rs2 known, reg_srli_exec_v7315 instruction pc rs1 rs2 known, reg_srli_exec_v7319 instruction pc rs1 rs2 known, reg_srli_exec_v7323 instruction pc rs1 rs2 known, reg_srli_exec_v7327 instruction pc rs1 rs2 known, reg_srli_exec_v7331 instruction pc rs1 rs2 known, reg_srli_exec_v7335 instruction pc rs1 rs2 known, reg_srli_exec_v7339 instruction pc rs1 rs2 known, reg_srli_exec_v7343 instruction pc rs1 rs2 known, reg_srli_exec_v7347 instruction pc rs1 rs2 known, reg_srli_exec_v7351 instruction pc rs1 rs2 known, reg_srli_exec_v7355 instruction pc rs1 rs2 known, reg_srli_exec_v7359 instruction pc rs1 rs2 known, reg_srli_exec_v7363 instruction pc rs1 rs2 known, reg_srli_exec_v7367 instruction pc rs1 rs2 known, reg_srli_exec_v7371 instruction pc rs1 rs2 known, reg_srli_exec_v7375 instruction pc rs1 rs2 known, reg_srli_exec_v7379 instruction pc rs1 rs2 known, reg_srli_exec_v7383 instruction pc rs1 rs2 known, reg_srli_exec_v7387 instruction pc rs1 rs2 known, reg_srli_exec_v7391 instruction pc rs1 rs2 known, reg_srli_exec_v7395 instruction pc rs1 rs2 known, reg_srli_exec_v7398 instruction pc rs1 rs2 known, reg_srli_exec_v7401 instruction pc rs1 rs2 known, exec_v7521, exec_v7791, exec_v7812, exec_v7813, exec_v7814, exec_v7815, exec_v7816, exec_v7817, exec_v7818, exec_v7819, exec_v7820, exec_v7821, exec_v7822, exec_v7823, exec_v7824, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7859, exec_v7860, exec_v7861, exec_v7862, exec_v7863, exec_v7864, exec_v7865, exec_v7866, exec_v7867, exec_v7868, exec_v7869, exec_v7870, exec_v7871, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7903, exec_v7904, exec_v7905, exec_v7906, exec_v7907, exec_v7908, exec_v7909, exec_v7910, exec_v7911, exec_v7912, exec_v7913, exec_v7914, exec_v7915, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7951, exec_v7952, exec_v7953, exec_v7954, exec_v7955, exec_v7956, exec_v7957, exec_v7958, exec_v7959, exec_v7960, exec_v7961, exec_v7962, exec_v7963, exec_v7964, exec_v7965, exec_v7966, exec_v7967, exec_v7968, exec_v7969, exec_v7970, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8013, exec_v8017, exec_v8018, exec_v8021, exec_v8022, exec_v8023, exec_v8024, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
  rw [dut_immediate_form instruction]
  simp [aluSpec, immediateI_low5]
#print axioms decoded_execution_srli
theorem writeback_execution_srli (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = ((writebackRs1 s).ushiftRight (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst).toNat) :=
  aligned.trans (decoded_execution_srli _ _ _ _ known)
#print axioms writeback_execution_srli
private theorem reg_srai_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 1073762323 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 1073762323 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 1073762323 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 1073762323 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 1073762323 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 1073762323 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 1073762323 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 1073762323 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 1073762323 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 1073762323 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7343 instruction pc rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 1073762323 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7347 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7347 instruction pc rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 1073762323 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7351 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7351 instruction pc rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 1073762323 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7355 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7355 instruction pc rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 1073762323 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7359 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7359 instruction pc rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 1073762323 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7363 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7363 instruction pc rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 1073762323 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7367 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7367 instruction pc rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 1073762323 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7371 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7371 instruction pc rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 1073762323 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7375 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7375 instruction pc rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 1073762323 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7379 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7379 instruction pc rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 1073762323 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7383 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7383 instruction pc rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 1073762323 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7387 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7387 instruction pc rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 1073762323 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7391 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7391 instruction pc rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 1073762323 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7395 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7395 instruction pc rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 1073762323 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7398 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7398 instruction pc rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 1073762323 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7401 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7401 instruction pc rs1 rs2 = 0 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20499 :=
    mask_incompatible instruction 4261441663 1073762323 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_exec_v7404 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : exec_v7404 instruction pc rs1 rs2 = 1 := by
  change (if (1073762323 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 1073762323 :=
    mask_refines instruction 4261441663 1073762323 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_srai (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) :
    decodedExecution instruction pc rs1 rs2 = (rs1.sshiftRight (BitVec.extractLsb' 20 5 instruction).toNat) := by
  simp only [decodedExecution, exec_v200, exec_v22, exec_v26, exec_v29, exec_v4, exec_v512, exec_v716, reg_srai_exec_v7303 instruction pc rs1 rs2 known, reg_srai_exec_v7307 instruction pc rs1 rs2 known, reg_srai_exec_v7311 instruction pc rs1 rs2 known, reg_srai_exec_v7315 instruction pc rs1 rs2 known, reg_srai_exec_v7319 instruction pc rs1 rs2 known, reg_srai_exec_v7323 instruction pc rs1 rs2 known, reg_srai_exec_v7327 instruction pc rs1 rs2 known, reg_srai_exec_v7331 instruction pc rs1 rs2 known, reg_srai_exec_v7335 instruction pc rs1 rs2 known, reg_srai_exec_v7339 instruction pc rs1 rs2 known, reg_srai_exec_v7343 instruction pc rs1 rs2 known, reg_srai_exec_v7347 instruction pc rs1 rs2 known, reg_srai_exec_v7351 instruction pc rs1 rs2 known, reg_srai_exec_v7355 instruction pc rs1 rs2 known, reg_srai_exec_v7359 instruction pc rs1 rs2 known, reg_srai_exec_v7363 instruction pc rs1 rs2 known, reg_srai_exec_v7367 instruction pc rs1 rs2 known, reg_srai_exec_v7371 instruction pc rs1 rs2 known, reg_srai_exec_v7375 instruction pc rs1 rs2 known, reg_srai_exec_v7379 instruction pc rs1 rs2 known, reg_srai_exec_v7383 instruction pc rs1 rs2 known, reg_srai_exec_v7387 instruction pc rs1 rs2 known, reg_srai_exec_v7391 instruction pc rs1 rs2 known, reg_srai_exec_v7395 instruction pc rs1 rs2 known, reg_srai_exec_v7398 instruction pc rs1 rs2 known, reg_srai_exec_v7401 instruction pc rs1 rs2 known, reg_srai_exec_v7404 instruction pc rs1 rs2 known, exec_v7521, exec_v7792, exec_v7811, exec_v7812, exec_v7813, exec_v7814, exec_v7815, exec_v7816, exec_v7817, exec_v7818, exec_v7819, exec_v7820, exec_v7821, exec_v7822, exec_v7823, exec_v7824, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7858, exec_v7859, exec_v7860, exec_v7861, exec_v7862, exec_v7863, exec_v7864, exec_v7865, exec_v7866, exec_v7867, exec_v7868, exec_v7869, exec_v7870, exec_v7871, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7902, exec_v7903, exec_v7904, exec_v7905, exec_v7906, exec_v7907, exec_v7908, exec_v7909, exec_v7910, exec_v7911, exec_v7912, exec_v7913, exec_v7914, exec_v7915, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7950, exec_v7951, exec_v7952, exec_v7953, exec_v7954, exec_v7955, exec_v7956, exec_v7957, exec_v7958, exec_v7959, exec_v7960, exec_v7961, exec_v7962, exec_v7963, exec_v7964, exec_v7965, exec_v7966, exec_v7967, exec_v7968, exec_v7969, exec_v7970, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8013, exec_v8017, exec_v8018, exec_v8021, exec_v8022, exec_v8023, exec_v8024, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
  rw [dut_immediate_form instruction]
  simp [aluSpec, immediateI_low5]
#print axioms decoded_execution_srai
theorem writeback_execution_srai (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = ((writebackRs1 s).sshiftRight (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst).toNat) :=
  aligned.trans (decoded_execution_srai _ _ _ _ known)
#print axioms writeback_execution_srai
end RiscvMiniProofs
