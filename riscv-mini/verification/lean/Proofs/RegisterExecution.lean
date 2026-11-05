import Proofs.ExecutionAlignment
import Proofs.MaskFacts
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
abbrev writebackRs1 (s : State) := dutRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst)
abbrev writebackRs2 (s : State) := dutRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst)
private theorem reg_add_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 51 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 51 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 51 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 51 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 51 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 51 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 51 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 51 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 51 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 51 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7343 instruction pc rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 51 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7347 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7347 instruction pc rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 51 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7351 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7351 instruction pc rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 51 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7355 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7355 instruction pc rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 51 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7359 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7359 instruction pc rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 51 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7363 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7363 instruction pc rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 51 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7367 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7367 instruction pc rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 51 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7371 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7371 instruction pc rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 51 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7375 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7375 instruction pc rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 51 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7379 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7379 instruction pc rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 51 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7383 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7383 instruction pc rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 51 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7387 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7387 instruction pc rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 51 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7391 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7391 instruction pc rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 51 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7395 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7395 instruction pc rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 51 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7398 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7398 instruction pc rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 51 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7401 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7401 instruction pc rs1 rs2 = 0 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20499 :=
    mask_incompatible instruction 4261441663 51 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7404 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7404 instruction pc rs1 rs2 = 0 := by
  change (if (1073762323 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762323 :=
    mask_incompatible instruction 4261441663 51 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_exec_v7407 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : exec_v7407 instruction pc rs1 rs2 = 1 := by
  change (if (51 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 51 :=
    mask_refines instruction 4261441663 51 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_add (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) :
    decodedExecution instruction pc rs1 rs2 = (rs1 + rs2) := by
  simp [decodedExecution, aluSpec, exec_v512, exec_v725, reg_add_exec_v7303 instruction pc rs1 rs2 known, reg_add_exec_v7307 instruction pc rs1 rs2 known, reg_add_exec_v7311 instruction pc rs1 rs2 known, reg_add_exec_v7315 instruction pc rs1 rs2 known, reg_add_exec_v7319 instruction pc rs1 rs2 known, reg_add_exec_v7323 instruction pc rs1 rs2 known, reg_add_exec_v7327 instruction pc rs1 rs2 known, reg_add_exec_v7331 instruction pc rs1 rs2 known, reg_add_exec_v7335 instruction pc rs1 rs2 known, reg_add_exec_v7339 instruction pc rs1 rs2 known, reg_add_exec_v7343 instruction pc rs1 rs2 known, reg_add_exec_v7347 instruction pc rs1 rs2 known, reg_add_exec_v7351 instruction pc rs1 rs2 known, reg_add_exec_v7355 instruction pc rs1 rs2 known, reg_add_exec_v7359 instruction pc rs1 rs2 known, reg_add_exec_v7363 instruction pc rs1 rs2 known, reg_add_exec_v7367 instruction pc rs1 rs2 known, reg_add_exec_v7371 instruction pc rs1 rs2 known, reg_add_exec_v7375 instruction pc rs1 rs2 known, reg_add_exec_v7379 instruction pc rs1 rs2 known, reg_add_exec_v7383 instruction pc rs1 rs2 known, reg_add_exec_v7387 instruction pc rs1 rs2 known, reg_add_exec_v7391 instruction pc rs1 rs2 known, reg_add_exec_v7395 instruction pc rs1 rs2 known, reg_add_exec_v7398 instruction pc rs1 rs2 known, reg_add_exec_v7401 instruction pc rs1 rs2 known, reg_add_exec_v7404 instruction pc rs1 rs2 known, reg_add_exec_v7407 instruction pc rs1 rs2 known, exec_v7810, exec_v7811, exec_v7812, exec_v7813, exec_v7814, exec_v7815, exec_v7816, exec_v7817, exec_v7818, exec_v7819, exec_v7820, exec_v7821, exec_v7822, exec_v7823, exec_v7824, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7857, exec_v7858, exec_v7859, exec_v7860, exec_v7861, exec_v7862, exec_v7863, exec_v7864, exec_v7865, exec_v7866, exec_v7867, exec_v7868, exec_v7869, exec_v7870, exec_v7871, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7901, exec_v7902, exec_v7903, exec_v7904, exec_v7905, exec_v7906, exec_v7907, exec_v7908, exec_v7909, exec_v7910, exec_v7911, exec_v7912, exec_v7913, exec_v7914, exec_v7915, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v8033, exec_v8034]
#print axioms decoded_execution_add
theorem writeback_execution_add (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = ((writebackRs1 s) + (writebackRs2 s)) :=
  aligned.trans (decoded_execution_add _ _ _ _ known)
#print axioms writeback_execution_add
private theorem reg_sub_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 1073741875 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 1073741875 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 1073741875 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 1073741875 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 1073741875 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 1073741875 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 1073741875 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 1073741875 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 1073741875 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 1073741875 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7343 instruction pc rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 1073741875 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7347 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7347 instruction pc rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 1073741875 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7351 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7351 instruction pc rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 1073741875 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7355 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7355 instruction pc rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 1073741875 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7359 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7359 instruction pc rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 1073741875 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7363 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7363 instruction pc rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 1073741875 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7367 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7367 instruction pc rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 1073741875 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7371 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7371 instruction pc rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 1073741875 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7375 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7375 instruction pc rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 1073741875 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7379 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7379 instruction pc rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 1073741875 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7383 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7383 instruction pc rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 1073741875 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7387 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7387 instruction pc rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 1073741875 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7391 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7391 instruction pc rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 1073741875 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7395 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7395 instruction pc rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 1073741875 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7398 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7398 instruction pc rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 1073741875 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7401 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7401 instruction pc rs1 rs2 = 0 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20499 :=
    mask_incompatible instruction 4261441663 1073741875 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7404 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7404 instruction pc rs1 rs2 = 0 := by
  change (if (1073762323 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762323 :=
    mask_incompatible instruction 4261441663 1073741875 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7407 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7407 instruction pc rs1 rs2 = 0 := by
  change (if (51 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 51 :=
    mask_incompatible instruction 4261441663 1073741875 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_exec_v7410 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : exec_v7410 instruction pc rs1 rs2 = 1 := by
  change (if (1073741875 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 1073741875 :=
    mask_refines instruction 4261441663 1073741875 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_sub (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) :
    decodedExecution instruction pc rs1 rs2 = (rs1 - rs2) := by
  simp [decodedExecution, aluSpec, exec_v512, reg_sub_exec_v7303 instruction pc rs1 rs2 known, reg_sub_exec_v7307 instruction pc rs1 rs2 known, reg_sub_exec_v7311 instruction pc rs1 rs2 known, reg_sub_exec_v7315 instruction pc rs1 rs2 known, reg_sub_exec_v7319 instruction pc rs1 rs2 known, reg_sub_exec_v7323 instruction pc rs1 rs2 known, reg_sub_exec_v7327 instruction pc rs1 rs2 known, reg_sub_exec_v7331 instruction pc rs1 rs2 known, reg_sub_exec_v7335 instruction pc rs1 rs2 known, reg_sub_exec_v7339 instruction pc rs1 rs2 known, reg_sub_exec_v7343 instruction pc rs1 rs2 known, reg_sub_exec_v7347 instruction pc rs1 rs2 known, reg_sub_exec_v7351 instruction pc rs1 rs2 known, reg_sub_exec_v7355 instruction pc rs1 rs2 known, reg_sub_exec_v7359 instruction pc rs1 rs2 known, reg_sub_exec_v7363 instruction pc rs1 rs2 known, reg_sub_exec_v7367 instruction pc rs1 rs2 known, reg_sub_exec_v7371 instruction pc rs1 rs2 known, reg_sub_exec_v7375 instruction pc rs1 rs2 known, reg_sub_exec_v7379 instruction pc rs1 rs2 known, reg_sub_exec_v7383 instruction pc rs1 rs2 known, reg_sub_exec_v7387 instruction pc rs1 rs2 known, reg_sub_exec_v7391 instruction pc rs1 rs2 known, reg_sub_exec_v7395 instruction pc rs1 rs2 known, reg_sub_exec_v7398 instruction pc rs1 rs2 known, reg_sub_exec_v7401 instruction pc rs1 rs2 known, reg_sub_exec_v7404 instruction pc rs1 rs2 known, reg_sub_exec_v7407 instruction pc rs1 rs2 known, reg_sub_exec_v7410 instruction pc rs1 rs2 known, exec_v7793, exec_v7809, exec_v7810, exec_v7811, exec_v7812, exec_v7813, exec_v7814, exec_v7815, exec_v7816, exec_v7817, exec_v7818, exec_v7819, exec_v7820, exec_v7821, exec_v7822, exec_v7823, exec_v7824, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7856, exec_v7857, exec_v7858, exec_v7859, exec_v7860, exec_v7861, exec_v7862, exec_v7863, exec_v7864, exec_v7865, exec_v7866, exec_v7867, exec_v7868, exec_v7869, exec_v7870, exec_v7871, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7900, exec_v7901, exec_v7902, exec_v7903, exec_v7904, exec_v7905, exec_v7906, exec_v7907, exec_v7908, exec_v7909, exec_v7910, exec_v7911, exec_v7912, exec_v7913, exec_v7914, exec_v7915, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v8033, exec_v8034]
#print axioms decoded_execution_sub
theorem writeback_execution_sub (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = ((writebackRs1 s) - (writebackRs2 s)) :=
  aligned.trans (decoded_execution_sub _ _ _ _ known)
#print axioms writeback_execution_sub
private theorem reg_sll_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 4147 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 4147 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 4147 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 4147 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 4147 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 4147 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 4147 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 4147 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 4147 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 4147 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7343 instruction pc rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 4147 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7347 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7347 instruction pc rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 4147 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7351 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7351 instruction pc rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 4147 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7355 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7355 instruction pc rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 4147 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7359 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7359 instruction pc rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 4147 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7363 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7363 instruction pc rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 4147 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7367 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7367 instruction pc rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 4147 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7371 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7371 instruction pc rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 4147 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7375 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7375 instruction pc rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 4147 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7379 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7379 instruction pc rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 4147 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7383 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7383 instruction pc rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 4147 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7387 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7387 instruction pc rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 4147 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7391 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7391 instruction pc rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 4147 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7395 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7395 instruction pc rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 4147 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7398 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7398 instruction pc rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 4147 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7401 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7401 instruction pc rs1 rs2 = 0 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20499 :=
    mask_incompatible instruction 4261441663 4147 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7404 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7404 instruction pc rs1 rs2 = 0 := by
  change (if (1073762323 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762323 :=
    mask_incompatible instruction 4261441663 4147 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7407 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7407 instruction pc rs1 rs2 = 0 := by
  change (if (51 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 51 :=
    mask_incompatible instruction 4261441663 4147 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7410 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7410 instruction pc rs1 rs2 = 0 := by
  change (if (1073741875 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073741875 :=
    mask_incompatible instruction 4261441663 4147 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_exec_v7413 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : exec_v7413 instruction pc rs1 rs2 = 1 := by
  change (if (4147 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 4147 :=
    mask_refines instruction 4261441663 4147 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_sll (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) :
    decodedExecution instruction pc rs1 rs2 = (rs1.shiftLeft (BitVec.extractLsb' 0 5 rs2).toNat) := by
  simp [decodedExecution, aluSpec, exec_v512, reg_sll_exec_v7303 instruction pc rs1 rs2 known, reg_sll_exec_v7307 instruction pc rs1 rs2 known, reg_sll_exec_v7311 instruction pc rs1 rs2 known, reg_sll_exec_v7315 instruction pc rs1 rs2 known, reg_sll_exec_v7319 instruction pc rs1 rs2 known, reg_sll_exec_v7323 instruction pc rs1 rs2 known, reg_sll_exec_v7327 instruction pc rs1 rs2 known, reg_sll_exec_v7331 instruction pc rs1 rs2 known, reg_sll_exec_v7335 instruction pc rs1 rs2 known, reg_sll_exec_v7339 instruction pc rs1 rs2 known, reg_sll_exec_v7343 instruction pc rs1 rs2 known, reg_sll_exec_v7347 instruction pc rs1 rs2 known, reg_sll_exec_v7351 instruction pc rs1 rs2 known, reg_sll_exec_v7355 instruction pc rs1 rs2 known, reg_sll_exec_v7359 instruction pc rs1 rs2 known, reg_sll_exec_v7363 instruction pc rs1 rs2 known, reg_sll_exec_v7367 instruction pc rs1 rs2 known, reg_sll_exec_v7371 instruction pc rs1 rs2 known, reg_sll_exec_v7375 instruction pc rs1 rs2 known, reg_sll_exec_v7379 instruction pc rs1 rs2 known, reg_sll_exec_v7383 instruction pc rs1 rs2 known, reg_sll_exec_v7387 instruction pc rs1 rs2 known, reg_sll_exec_v7391 instruction pc rs1 rs2 known, reg_sll_exec_v7395 instruction pc rs1 rs2 known, reg_sll_exec_v7398 instruction pc rs1 rs2 known, reg_sll_exec_v7401 instruction pc rs1 rs2 known, reg_sll_exec_v7404 instruction pc rs1 rs2 known, reg_sll_exec_v7407 instruction pc rs1 rs2 known, reg_sll_exec_v7410 instruction pc rs1 rs2 known, reg_sll_exec_v7413 instruction pc rs1 rs2 known, exec_v7790, exec_v7808, exec_v7809, exec_v7810, exec_v7811, exec_v7812, exec_v7813, exec_v7814, exec_v7815, exec_v7816, exec_v7817, exec_v7818, exec_v7819, exec_v7820, exec_v7821, exec_v7822, exec_v7823, exec_v7824, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7855, exec_v7856, exec_v7857, exec_v7858, exec_v7859, exec_v7860, exec_v7861, exec_v7862, exec_v7863, exec_v7864, exec_v7865, exec_v7866, exec_v7867, exec_v7868, exec_v7869, exec_v7870, exec_v7871, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7899, exec_v7900, exec_v7901, exec_v7902, exec_v7903, exec_v7904, exec_v7905, exec_v7906, exec_v7907, exec_v7908, exec_v7909, exec_v7910, exec_v7911, exec_v7912, exec_v7913, exec_v7914, exec_v7915, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v8033, exec_v8034]
#print axioms decoded_execution_sll
theorem writeback_execution_sll (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = ((writebackRs1 s).shiftLeft (BitVec.extractLsb' 0 5 (writebackRs2 s)).toNat) :=
  aligned.trans (decoded_execution_sll _ _ _ _ known)
#print axioms writeback_execution_sll
private theorem reg_slt_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 8243 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 8243 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 8243 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 8243 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 8243 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 8243 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 8243 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 8243 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 8243 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 8243 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7343 instruction pc rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 8243 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7347 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7347 instruction pc rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 8243 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7351 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7351 instruction pc rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 8243 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7355 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7355 instruction pc rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 8243 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7359 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7359 instruction pc rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 8243 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7363 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7363 instruction pc rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 8243 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7367 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7367 instruction pc rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 8243 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7371 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7371 instruction pc rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 8243 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7375 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7375 instruction pc rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 8243 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7379 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7379 instruction pc rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 8243 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7383 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7383 instruction pc rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 8243 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7387 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7387 instruction pc rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 8243 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7391 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7391 instruction pc rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 8243 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7395 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7395 instruction pc rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 8243 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7398 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7398 instruction pc rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 8243 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7401 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7401 instruction pc rs1 rs2 = 0 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20499 :=
    mask_incompatible instruction 4261441663 8243 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7404 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7404 instruction pc rs1 rs2 = 0 := by
  change (if (1073762323 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762323 :=
    mask_incompatible instruction 4261441663 8243 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7407 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7407 instruction pc rs1 rs2 = 0 := by
  change (if (51 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 51 :=
    mask_incompatible instruction 4261441663 8243 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7410 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7410 instruction pc rs1 rs2 = 0 := by
  change (if (1073741875 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073741875 :=
    mask_incompatible instruction 4261441663 8243 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7413 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7413 instruction pc rs1 rs2 = 0 := by
  change (if (4147 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4147 :=
    mask_incompatible instruction 4261441663 8243 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_exec_v7416 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : exec_v7416 instruction pc rs1 rs2 = 1 := by
  change (if (8243 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 8243 :=
    mask_refines instruction 4261441663 8243 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_slt (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) :
    decodedExecution instruction pc rs1 rs2 = (if rs1.toInt < rs2.toInt then 1 else 0) := by
  simp [decodedExecution, aluSpec, exec_v512, reg_slt_exec_v7303 instruction pc rs1 rs2 known, reg_slt_exec_v7307 instruction pc rs1 rs2 known, reg_slt_exec_v7311 instruction pc rs1 rs2 known, reg_slt_exec_v7315 instruction pc rs1 rs2 known, reg_slt_exec_v7319 instruction pc rs1 rs2 known, reg_slt_exec_v7323 instruction pc rs1 rs2 known, reg_slt_exec_v7327 instruction pc rs1 rs2 known, reg_slt_exec_v7331 instruction pc rs1 rs2 known, reg_slt_exec_v7335 instruction pc rs1 rs2 known, reg_slt_exec_v7339 instruction pc rs1 rs2 known, reg_slt_exec_v7343 instruction pc rs1 rs2 known, reg_slt_exec_v7347 instruction pc rs1 rs2 known, reg_slt_exec_v7351 instruction pc rs1 rs2 known, reg_slt_exec_v7355 instruction pc rs1 rs2 known, reg_slt_exec_v7359 instruction pc rs1 rs2 known, reg_slt_exec_v7363 instruction pc rs1 rs2 known, reg_slt_exec_v7367 instruction pc rs1 rs2 known, reg_slt_exec_v7371 instruction pc rs1 rs2 known, reg_slt_exec_v7375 instruction pc rs1 rs2 known, reg_slt_exec_v7379 instruction pc rs1 rs2 known, reg_slt_exec_v7383 instruction pc rs1 rs2 known, reg_slt_exec_v7387 instruction pc rs1 rs2 known, reg_slt_exec_v7391 instruction pc rs1 rs2 known, reg_slt_exec_v7395 instruction pc rs1 rs2 known, reg_slt_exec_v7398 instruction pc rs1 rs2 known, reg_slt_exec_v7401 instruction pc rs1 rs2 known, reg_slt_exec_v7404 instruction pc rs1 rs2 known, reg_slt_exec_v7407 instruction pc rs1 rs2 known, reg_slt_exec_v7410 instruction pc rs1 rs2 known, reg_slt_exec_v7413 instruction pc rs1 rs2 known, reg_slt_exec_v7416 instruction pc rs1 rs2 known, exec_v7785, exec_v7807, exec_v7808, exec_v7809, exec_v7810, exec_v7811, exec_v7812, exec_v7813, exec_v7814, exec_v7815, exec_v7816, exec_v7817, exec_v7818, exec_v7819, exec_v7820, exec_v7821, exec_v7822, exec_v7823, exec_v7824, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7854, exec_v7855, exec_v7856, exec_v7857, exec_v7858, exec_v7859, exec_v7860, exec_v7861, exec_v7862, exec_v7863, exec_v7864, exec_v7865, exec_v7866, exec_v7867, exec_v7868, exec_v7869, exec_v7870, exec_v7871, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7898, exec_v7899, exec_v7900, exec_v7901, exec_v7902, exec_v7903, exec_v7904, exec_v7905, exec_v7906, exec_v7907, exec_v7908, exec_v7909, exec_v7910, exec_v7911, exec_v7912, exec_v7913, exec_v7914, exec_v7915, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v8033, exec_v8034]
#print axioms decoded_execution_slt
theorem writeback_execution_slt (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = (if (writebackRs1 s).toInt < (writebackRs2 s).toInt then 1 else 0) :=
  aligned.trans (decoded_execution_slt _ _ _ _ known)
#print axioms writeback_execution_slt
private theorem reg_sltu_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 12339 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 12339 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 12339 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 12339 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 12339 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 12339 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 12339 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 12339 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 12339 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 12339 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7343 instruction pc rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 12339 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7347 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7347 instruction pc rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 12339 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7351 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7351 instruction pc rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 12339 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7355 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7355 instruction pc rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 12339 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7359 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7359 instruction pc rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 12339 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7363 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7363 instruction pc rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 12339 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7367 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7367 instruction pc rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 12339 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7371 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7371 instruction pc rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 12339 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7375 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7375 instruction pc rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 12339 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7379 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7379 instruction pc rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 12339 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7383 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7383 instruction pc rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 12339 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7387 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7387 instruction pc rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 12339 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7391 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7391 instruction pc rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 12339 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7395 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7395 instruction pc rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 12339 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7398 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7398 instruction pc rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 12339 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7401 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7401 instruction pc rs1 rs2 = 0 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20499 :=
    mask_incompatible instruction 4261441663 12339 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7404 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7404 instruction pc rs1 rs2 = 0 := by
  change (if (1073762323 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762323 :=
    mask_incompatible instruction 4261441663 12339 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7407 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7407 instruction pc rs1 rs2 = 0 := by
  change (if (51 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 51 :=
    mask_incompatible instruction 4261441663 12339 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7410 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7410 instruction pc rs1 rs2 = 0 := by
  change (if (1073741875 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073741875 :=
    mask_incompatible instruction 4261441663 12339 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7413 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7413 instruction pc rs1 rs2 = 0 := by
  change (if (4147 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4147 :=
    mask_incompatible instruction 4261441663 12339 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7416 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7416 instruction pc rs1 rs2 = 0 := by
  change (if (8243 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 8243 :=
    mask_incompatible instruction 4261441663 12339 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_exec_v7419 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : exec_v7419 instruction pc rs1 rs2 = 1 := by
  change (if (12339 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 12339 :=
    mask_refines instruction 4261441663 12339 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_sltu (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) :
    decodedExecution instruction pc rs1 rs2 = (if rs1.toNat < rs2.toNat then 1 else 0) := by
  simp [decodedExecution, aluSpec, exec_v512, reg_sltu_exec_v7303 instruction pc rs1 rs2 known, reg_sltu_exec_v7307 instruction pc rs1 rs2 known, reg_sltu_exec_v7311 instruction pc rs1 rs2 known, reg_sltu_exec_v7315 instruction pc rs1 rs2 known, reg_sltu_exec_v7319 instruction pc rs1 rs2 known, reg_sltu_exec_v7323 instruction pc rs1 rs2 known, reg_sltu_exec_v7327 instruction pc rs1 rs2 known, reg_sltu_exec_v7331 instruction pc rs1 rs2 known, reg_sltu_exec_v7335 instruction pc rs1 rs2 known, reg_sltu_exec_v7339 instruction pc rs1 rs2 known, reg_sltu_exec_v7343 instruction pc rs1 rs2 known, reg_sltu_exec_v7347 instruction pc rs1 rs2 known, reg_sltu_exec_v7351 instruction pc rs1 rs2 known, reg_sltu_exec_v7355 instruction pc rs1 rs2 known, reg_sltu_exec_v7359 instruction pc rs1 rs2 known, reg_sltu_exec_v7363 instruction pc rs1 rs2 known, reg_sltu_exec_v7367 instruction pc rs1 rs2 known, reg_sltu_exec_v7371 instruction pc rs1 rs2 known, reg_sltu_exec_v7375 instruction pc rs1 rs2 known, reg_sltu_exec_v7379 instruction pc rs1 rs2 known, reg_sltu_exec_v7383 instruction pc rs1 rs2 known, reg_sltu_exec_v7387 instruction pc rs1 rs2 known, reg_sltu_exec_v7391 instruction pc rs1 rs2 known, reg_sltu_exec_v7395 instruction pc rs1 rs2 known, reg_sltu_exec_v7398 instruction pc rs1 rs2 known, reg_sltu_exec_v7401 instruction pc rs1 rs2 known, reg_sltu_exec_v7404 instruction pc rs1 rs2 known, reg_sltu_exec_v7407 instruction pc rs1 rs2 known, reg_sltu_exec_v7410 instruction pc rs1 rs2 known, reg_sltu_exec_v7413 instruction pc rs1 rs2 known, reg_sltu_exec_v7416 instruction pc rs1 rs2 known, reg_sltu_exec_v7419 instruction pc rs1 rs2 known, exec_v7786, exec_v7806, exec_v7807, exec_v7808, exec_v7809, exec_v7810, exec_v7811, exec_v7812, exec_v7813, exec_v7814, exec_v7815, exec_v7816, exec_v7817, exec_v7818, exec_v7819, exec_v7820, exec_v7821, exec_v7822, exec_v7823, exec_v7824, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7853, exec_v7854, exec_v7855, exec_v7856, exec_v7857, exec_v7858, exec_v7859, exec_v7860, exec_v7861, exec_v7862, exec_v7863, exec_v7864, exec_v7865, exec_v7866, exec_v7867, exec_v7868, exec_v7869, exec_v7870, exec_v7871, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7897, exec_v7898, exec_v7899, exec_v7900, exec_v7901, exec_v7902, exec_v7903, exec_v7904, exec_v7905, exec_v7906, exec_v7907, exec_v7908, exec_v7909, exec_v7910, exec_v7911, exec_v7912, exec_v7913, exec_v7914, exec_v7915, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v8033, exec_v8034]
#print axioms decoded_execution_sltu
theorem writeback_execution_sltu (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = (if (writebackRs1 s).toNat < (writebackRs2 s).toNat then 1 else 0) :=
  aligned.trans (decoded_execution_sltu _ _ _ _ known)
#print axioms writeback_execution_sltu
private theorem reg_xor_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 16435 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 16435 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 16435 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 16435 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 16435 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 16435 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 16435 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 16435 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 16435 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 16435 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7343 instruction pc rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 16435 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7347 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7347 instruction pc rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 16435 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7351 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7351 instruction pc rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 16435 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7355 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7355 instruction pc rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 16435 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7359 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7359 instruction pc rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 16435 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7363 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7363 instruction pc rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 16435 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7367 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7367 instruction pc rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 16435 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7371 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7371 instruction pc rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 16435 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7375 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7375 instruction pc rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 16435 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7379 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7379 instruction pc rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 16435 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7383 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7383 instruction pc rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 16435 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7387 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7387 instruction pc rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 16435 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7391 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7391 instruction pc rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 16435 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7395 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7395 instruction pc rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 16435 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7398 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7398 instruction pc rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 16435 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7401 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7401 instruction pc rs1 rs2 = 0 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20499 :=
    mask_incompatible instruction 4261441663 16435 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7404 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7404 instruction pc rs1 rs2 = 0 := by
  change (if (1073762323 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762323 :=
    mask_incompatible instruction 4261441663 16435 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7407 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7407 instruction pc rs1 rs2 = 0 := by
  change (if (51 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 51 :=
    mask_incompatible instruction 4261441663 16435 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7410 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7410 instruction pc rs1 rs2 = 0 := by
  change (if (1073741875 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073741875 :=
    mask_incompatible instruction 4261441663 16435 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7413 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7413 instruction pc rs1 rs2 = 0 := by
  change (if (4147 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4147 :=
    mask_incompatible instruction 4261441663 16435 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7416 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7416 instruction pc rs1 rs2 = 0 := by
  change (if (8243 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 8243 :=
    mask_incompatible instruction 4261441663 16435 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7419 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7419 instruction pc rs1 rs2 = 0 := by
  change (if (12339 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 12339 :=
    mask_incompatible instruction 4261441663 16435 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_exec_v7422 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : exec_v7422 instruction pc rs1 rs2 = 1 := by
  change (if (16435 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 16435 :=
    mask_refines instruction 4261441663 16435 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_xor (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) :
    decodedExecution instruction pc rs1 rs2 = (rs1 ^^^ rs2) := by
  simp [decodedExecution, aluSpec, exec_v512, reg_xor_exec_v7303 instruction pc rs1 rs2 known, reg_xor_exec_v7307 instruction pc rs1 rs2 known, reg_xor_exec_v7311 instruction pc rs1 rs2 known, reg_xor_exec_v7315 instruction pc rs1 rs2 known, reg_xor_exec_v7319 instruction pc rs1 rs2 known, reg_xor_exec_v7323 instruction pc rs1 rs2 known, reg_xor_exec_v7327 instruction pc rs1 rs2 known, reg_xor_exec_v7331 instruction pc rs1 rs2 known, reg_xor_exec_v7335 instruction pc rs1 rs2 known, reg_xor_exec_v7339 instruction pc rs1 rs2 known, reg_xor_exec_v7343 instruction pc rs1 rs2 known, reg_xor_exec_v7347 instruction pc rs1 rs2 known, reg_xor_exec_v7351 instruction pc rs1 rs2 known, reg_xor_exec_v7355 instruction pc rs1 rs2 known, reg_xor_exec_v7359 instruction pc rs1 rs2 known, reg_xor_exec_v7363 instruction pc rs1 rs2 known, reg_xor_exec_v7367 instruction pc rs1 rs2 known, reg_xor_exec_v7371 instruction pc rs1 rs2 known, reg_xor_exec_v7375 instruction pc rs1 rs2 known, reg_xor_exec_v7379 instruction pc rs1 rs2 known, reg_xor_exec_v7383 instruction pc rs1 rs2 known, reg_xor_exec_v7387 instruction pc rs1 rs2 known, reg_xor_exec_v7391 instruction pc rs1 rs2 known, reg_xor_exec_v7395 instruction pc rs1 rs2 known, reg_xor_exec_v7398 instruction pc rs1 rs2 known, reg_xor_exec_v7401 instruction pc rs1 rs2 known, reg_xor_exec_v7404 instruction pc rs1 rs2 known, reg_xor_exec_v7407 instruction pc rs1 rs2 known, reg_xor_exec_v7410 instruction pc rs1 rs2 known, reg_xor_exec_v7413 instruction pc rs1 rs2 known, reg_xor_exec_v7416 instruction pc rs1 rs2 known, reg_xor_exec_v7419 instruction pc rs1 rs2 known, reg_xor_exec_v7422 instruction pc rs1 rs2 known, exec_v7787, exec_v7805, exec_v7806, exec_v7807, exec_v7808, exec_v7809, exec_v7810, exec_v7811, exec_v7812, exec_v7813, exec_v7814, exec_v7815, exec_v7816, exec_v7817, exec_v7818, exec_v7819, exec_v7820, exec_v7821, exec_v7822, exec_v7823, exec_v7824, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7852, exec_v7853, exec_v7854, exec_v7855, exec_v7856, exec_v7857, exec_v7858, exec_v7859, exec_v7860, exec_v7861, exec_v7862, exec_v7863, exec_v7864, exec_v7865, exec_v7866, exec_v7867, exec_v7868, exec_v7869, exec_v7870, exec_v7871, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7896, exec_v7897, exec_v7898, exec_v7899, exec_v7900, exec_v7901, exec_v7902, exec_v7903, exec_v7904, exec_v7905, exec_v7906, exec_v7907, exec_v7908, exec_v7909, exec_v7910, exec_v7911, exec_v7912, exec_v7913, exec_v7914, exec_v7915, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v8033, exec_v8034]
#print axioms decoded_execution_xor
theorem writeback_execution_xor (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = ((writebackRs1 s) ^^^ (writebackRs2 s)) :=
  aligned.trans (decoded_execution_xor _ _ _ _ known)
#print axioms writeback_execution_xor
private theorem reg_srl_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 20531 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 20531 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 20531 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 20531 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 20531 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 20531 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 20531 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 20531 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 20531 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 20531 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7343 instruction pc rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 20531 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7347 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7347 instruction pc rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 20531 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7351 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7351 instruction pc rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 20531 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7355 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7355 instruction pc rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 20531 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7359 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7359 instruction pc rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 20531 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7363 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7363 instruction pc rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 20531 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7367 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7367 instruction pc rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 20531 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7371 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7371 instruction pc rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 20531 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7375 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7375 instruction pc rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 20531 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7379 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7379 instruction pc rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 20531 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7383 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7383 instruction pc rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 20531 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7387 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7387 instruction pc rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 20531 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7391 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7391 instruction pc rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 20531 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7395 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7395 instruction pc rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 20531 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7398 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7398 instruction pc rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 20531 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7401 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7401 instruction pc rs1 rs2 = 0 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20499 :=
    mask_incompatible instruction 4261441663 20531 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7404 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7404 instruction pc rs1 rs2 = 0 := by
  change (if (1073762323 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762323 :=
    mask_incompatible instruction 4261441663 20531 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7407 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7407 instruction pc rs1 rs2 = 0 := by
  change (if (51 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 51 :=
    mask_incompatible instruction 4261441663 20531 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7410 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7410 instruction pc rs1 rs2 = 0 := by
  change (if (1073741875 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073741875 :=
    mask_incompatible instruction 4261441663 20531 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7413 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7413 instruction pc rs1 rs2 = 0 := by
  change (if (4147 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4147 :=
    mask_incompatible instruction 4261441663 20531 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7416 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7416 instruction pc rs1 rs2 = 0 := by
  change (if (8243 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 8243 :=
    mask_incompatible instruction 4261441663 20531 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7419 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7419 instruction pc rs1 rs2 = 0 := by
  change (if (12339 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 12339 :=
    mask_incompatible instruction 4261441663 20531 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7422 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7422 instruction pc rs1 rs2 = 0 := by
  change (if (16435 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 16435 :=
    mask_incompatible instruction 4261441663 20531 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_exec_v7425 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : exec_v7425 instruction pc rs1 rs2 = 1 := by
  change (if (20531 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 20531 :=
    mask_refines instruction 4261441663 20531 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_srl (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) :
    decodedExecution instruction pc rs1 rs2 = (rs1.ushiftRight (BitVec.extractLsb' 0 5 rs2).toNat) := by
  simp [decodedExecution, aluSpec, exec_v512, reg_srl_exec_v7303 instruction pc rs1 rs2 known, reg_srl_exec_v7307 instruction pc rs1 rs2 known, reg_srl_exec_v7311 instruction pc rs1 rs2 known, reg_srl_exec_v7315 instruction pc rs1 rs2 known, reg_srl_exec_v7319 instruction pc rs1 rs2 known, reg_srl_exec_v7323 instruction pc rs1 rs2 known, reg_srl_exec_v7327 instruction pc rs1 rs2 known, reg_srl_exec_v7331 instruction pc rs1 rs2 known, reg_srl_exec_v7335 instruction pc rs1 rs2 known, reg_srl_exec_v7339 instruction pc rs1 rs2 known, reg_srl_exec_v7343 instruction pc rs1 rs2 known, reg_srl_exec_v7347 instruction pc rs1 rs2 known, reg_srl_exec_v7351 instruction pc rs1 rs2 known, reg_srl_exec_v7355 instruction pc rs1 rs2 known, reg_srl_exec_v7359 instruction pc rs1 rs2 known, reg_srl_exec_v7363 instruction pc rs1 rs2 known, reg_srl_exec_v7367 instruction pc rs1 rs2 known, reg_srl_exec_v7371 instruction pc rs1 rs2 known, reg_srl_exec_v7375 instruction pc rs1 rs2 known, reg_srl_exec_v7379 instruction pc rs1 rs2 known, reg_srl_exec_v7383 instruction pc rs1 rs2 known, reg_srl_exec_v7387 instruction pc rs1 rs2 known, reg_srl_exec_v7391 instruction pc rs1 rs2 known, reg_srl_exec_v7395 instruction pc rs1 rs2 known, reg_srl_exec_v7398 instruction pc rs1 rs2 known, reg_srl_exec_v7401 instruction pc rs1 rs2 known, reg_srl_exec_v7404 instruction pc rs1 rs2 known, reg_srl_exec_v7407 instruction pc rs1 rs2 known, reg_srl_exec_v7410 instruction pc rs1 rs2 known, reg_srl_exec_v7413 instruction pc rs1 rs2 known, reg_srl_exec_v7416 instruction pc rs1 rs2 known, reg_srl_exec_v7419 instruction pc rs1 rs2 known, reg_srl_exec_v7422 instruction pc rs1 rs2 known, reg_srl_exec_v7425 instruction pc rs1 rs2 known, exec_v7791, exec_v7804, exec_v7805, exec_v7806, exec_v7807, exec_v7808, exec_v7809, exec_v7810, exec_v7811, exec_v7812, exec_v7813, exec_v7814, exec_v7815, exec_v7816, exec_v7817, exec_v7818, exec_v7819, exec_v7820, exec_v7821, exec_v7822, exec_v7823, exec_v7824, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7851, exec_v7852, exec_v7853, exec_v7854, exec_v7855, exec_v7856, exec_v7857, exec_v7858, exec_v7859, exec_v7860, exec_v7861, exec_v7862, exec_v7863, exec_v7864, exec_v7865, exec_v7866, exec_v7867, exec_v7868, exec_v7869, exec_v7870, exec_v7871, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7895, exec_v7896, exec_v7897, exec_v7898, exec_v7899, exec_v7900, exec_v7901, exec_v7902, exec_v7903, exec_v7904, exec_v7905, exec_v7906, exec_v7907, exec_v7908, exec_v7909, exec_v7910, exec_v7911, exec_v7912, exec_v7913, exec_v7914, exec_v7915, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v8033, exec_v8034]
#print axioms decoded_execution_srl
theorem writeback_execution_srl (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = ((writebackRs1 s).ushiftRight (BitVec.extractLsb' 0 5 (writebackRs2 s)).toNat) :=
  aligned.trans (decoded_execution_srl _ _ _ _ known)
#print axioms writeback_execution_srl
private theorem reg_sra_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 1073762355 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 1073762355 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 1073762355 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 1073762355 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 1073762355 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 1073762355 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 1073762355 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 1073762355 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 1073762355 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 1073762355 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7343 instruction pc rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 1073762355 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7347 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7347 instruction pc rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 1073762355 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7351 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7351 instruction pc rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 1073762355 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7355 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7355 instruction pc rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 1073762355 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7359 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7359 instruction pc rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 1073762355 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7363 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7363 instruction pc rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 1073762355 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7367 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7367 instruction pc rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 1073762355 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7371 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7371 instruction pc rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 1073762355 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7375 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7375 instruction pc rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 1073762355 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7379 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7379 instruction pc rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 1073762355 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7383 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7383 instruction pc rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 1073762355 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7387 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7387 instruction pc rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 1073762355 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7391 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7391 instruction pc rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 1073762355 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7395 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7395 instruction pc rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 1073762355 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7398 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7398 instruction pc rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 1073762355 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7401 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7401 instruction pc rs1 rs2 = 0 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20499 :=
    mask_incompatible instruction 4261441663 1073762355 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7404 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7404 instruction pc rs1 rs2 = 0 := by
  change (if (1073762323 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762323 :=
    mask_incompatible instruction 4261441663 1073762355 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7407 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7407 instruction pc rs1 rs2 = 0 := by
  change (if (51 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 51 :=
    mask_incompatible instruction 4261441663 1073762355 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7410 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7410 instruction pc rs1 rs2 = 0 := by
  change (if (1073741875 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073741875 :=
    mask_incompatible instruction 4261441663 1073762355 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7413 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7413 instruction pc rs1 rs2 = 0 := by
  change (if (4147 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4147 :=
    mask_incompatible instruction 4261441663 1073762355 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7416 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7416 instruction pc rs1 rs2 = 0 := by
  change (if (8243 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 8243 :=
    mask_incompatible instruction 4261441663 1073762355 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7419 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7419 instruction pc rs1 rs2 = 0 := by
  change (if (12339 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 12339 :=
    mask_incompatible instruction 4261441663 1073762355 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7422 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7422 instruction pc rs1 rs2 = 0 := by
  change (if (16435 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 16435 :=
    mask_incompatible instruction 4261441663 1073762355 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7425 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7425 instruction pc rs1 rs2 = 0 := by
  change (if (20531 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20531 :=
    mask_incompatible instruction 4261441663 1073762355 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_exec_v7428 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : exec_v7428 instruction pc rs1 rs2 = 1 := by
  change (if (1073762355 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 1073762355 :=
    mask_refines instruction 4261441663 1073762355 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_sra (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) :
    decodedExecution instruction pc rs1 rs2 = (rs1.sshiftRight (BitVec.extractLsb' 0 5 rs2).toNat) := by
  simp [decodedExecution, aluSpec, exec_v512, reg_sra_exec_v7303 instruction pc rs1 rs2 known, reg_sra_exec_v7307 instruction pc rs1 rs2 known, reg_sra_exec_v7311 instruction pc rs1 rs2 known, reg_sra_exec_v7315 instruction pc rs1 rs2 known, reg_sra_exec_v7319 instruction pc rs1 rs2 known, reg_sra_exec_v7323 instruction pc rs1 rs2 known, reg_sra_exec_v7327 instruction pc rs1 rs2 known, reg_sra_exec_v7331 instruction pc rs1 rs2 known, reg_sra_exec_v7335 instruction pc rs1 rs2 known, reg_sra_exec_v7339 instruction pc rs1 rs2 known, reg_sra_exec_v7343 instruction pc rs1 rs2 known, reg_sra_exec_v7347 instruction pc rs1 rs2 known, reg_sra_exec_v7351 instruction pc rs1 rs2 known, reg_sra_exec_v7355 instruction pc rs1 rs2 known, reg_sra_exec_v7359 instruction pc rs1 rs2 known, reg_sra_exec_v7363 instruction pc rs1 rs2 known, reg_sra_exec_v7367 instruction pc rs1 rs2 known, reg_sra_exec_v7371 instruction pc rs1 rs2 known, reg_sra_exec_v7375 instruction pc rs1 rs2 known, reg_sra_exec_v7379 instruction pc rs1 rs2 known, reg_sra_exec_v7383 instruction pc rs1 rs2 known, reg_sra_exec_v7387 instruction pc rs1 rs2 known, reg_sra_exec_v7391 instruction pc rs1 rs2 known, reg_sra_exec_v7395 instruction pc rs1 rs2 known, reg_sra_exec_v7398 instruction pc rs1 rs2 known, reg_sra_exec_v7401 instruction pc rs1 rs2 known, reg_sra_exec_v7404 instruction pc rs1 rs2 known, reg_sra_exec_v7407 instruction pc rs1 rs2 known, reg_sra_exec_v7410 instruction pc rs1 rs2 known, reg_sra_exec_v7413 instruction pc rs1 rs2 known, reg_sra_exec_v7416 instruction pc rs1 rs2 known, reg_sra_exec_v7419 instruction pc rs1 rs2 known, reg_sra_exec_v7422 instruction pc rs1 rs2 known, reg_sra_exec_v7425 instruction pc rs1 rs2 known, reg_sra_exec_v7428 instruction pc rs1 rs2 known, exec_v7792, exec_v7803, exec_v7804, exec_v7805, exec_v7806, exec_v7807, exec_v7808, exec_v7809, exec_v7810, exec_v7811, exec_v7812, exec_v7813, exec_v7814, exec_v7815, exec_v7816, exec_v7817, exec_v7818, exec_v7819, exec_v7820, exec_v7821, exec_v7822, exec_v7823, exec_v7824, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7850, exec_v7851, exec_v7852, exec_v7853, exec_v7854, exec_v7855, exec_v7856, exec_v7857, exec_v7858, exec_v7859, exec_v7860, exec_v7861, exec_v7862, exec_v7863, exec_v7864, exec_v7865, exec_v7866, exec_v7867, exec_v7868, exec_v7869, exec_v7870, exec_v7871, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7894, exec_v7895, exec_v7896, exec_v7897, exec_v7898, exec_v7899, exec_v7900, exec_v7901, exec_v7902, exec_v7903, exec_v7904, exec_v7905, exec_v7906, exec_v7907, exec_v7908, exec_v7909, exec_v7910, exec_v7911, exec_v7912, exec_v7913, exec_v7914, exec_v7915, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v8033, exec_v8034]
#print axioms decoded_execution_sra
theorem writeback_execution_sra (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = ((writebackRs1 s).sshiftRight (BitVec.extractLsb' 0 5 (writebackRs2 s)).toNat) :=
  aligned.trans (decoded_execution_sra _ _ _ _ known)
#print axioms writeback_execution_sra
private theorem reg_or_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 24627 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 24627 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 24627 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 24627 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 24627 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 24627 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 24627 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 24627 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 24627 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 24627 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7343 instruction pc rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 24627 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7347 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7347 instruction pc rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 24627 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7351 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7351 instruction pc rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 24627 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7355 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7355 instruction pc rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 24627 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7359 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7359 instruction pc rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 24627 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7363 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7363 instruction pc rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 24627 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7367 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7367 instruction pc rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 24627 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7371 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7371 instruction pc rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 24627 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7375 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7375 instruction pc rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 24627 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7379 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7379 instruction pc rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 24627 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7383 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7383 instruction pc rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 24627 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7387 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7387 instruction pc rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 24627 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7391 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7391 instruction pc rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 24627 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7395 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7395 instruction pc rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 24627 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7398 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7398 instruction pc rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 24627 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7401 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7401 instruction pc rs1 rs2 = 0 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20499 :=
    mask_incompatible instruction 4261441663 24627 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7404 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7404 instruction pc rs1 rs2 = 0 := by
  change (if (1073762323 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762323 :=
    mask_incompatible instruction 4261441663 24627 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7407 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7407 instruction pc rs1 rs2 = 0 := by
  change (if (51 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 51 :=
    mask_incompatible instruction 4261441663 24627 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7410 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7410 instruction pc rs1 rs2 = 0 := by
  change (if (1073741875 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073741875 :=
    mask_incompatible instruction 4261441663 24627 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7413 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7413 instruction pc rs1 rs2 = 0 := by
  change (if (4147 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4147 :=
    mask_incompatible instruction 4261441663 24627 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7416 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7416 instruction pc rs1 rs2 = 0 := by
  change (if (8243 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 8243 :=
    mask_incompatible instruction 4261441663 24627 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7419 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7419 instruction pc rs1 rs2 = 0 := by
  change (if (12339 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 12339 :=
    mask_incompatible instruction 4261441663 24627 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7422 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7422 instruction pc rs1 rs2 = 0 := by
  change (if (16435 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 16435 :=
    mask_incompatible instruction 4261441663 24627 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7425 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7425 instruction pc rs1 rs2 = 0 := by
  change (if (20531 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20531 :=
    mask_incompatible instruction 4261441663 24627 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7428 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7428 instruction pc rs1 rs2 = 0 := by
  change (if (1073762355 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762355 :=
    mask_incompatible instruction 4261441663 24627 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_exec_v7431 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : exec_v7431 instruction pc rs1 rs2 = 1 := by
  change (if (24627 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 24627 :=
    mask_refines instruction 4261441663 24627 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_or (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) :
    decodedExecution instruction pc rs1 rs2 = (rs1 ||| rs2) := by
  simp [decodedExecution, aluSpec, exec_v512, reg_or_exec_v7303 instruction pc rs1 rs2 known, reg_or_exec_v7307 instruction pc rs1 rs2 known, reg_or_exec_v7311 instruction pc rs1 rs2 known, reg_or_exec_v7315 instruction pc rs1 rs2 known, reg_or_exec_v7319 instruction pc rs1 rs2 known, reg_or_exec_v7323 instruction pc rs1 rs2 known, reg_or_exec_v7327 instruction pc rs1 rs2 known, reg_or_exec_v7331 instruction pc rs1 rs2 known, reg_or_exec_v7335 instruction pc rs1 rs2 known, reg_or_exec_v7339 instruction pc rs1 rs2 known, reg_or_exec_v7343 instruction pc rs1 rs2 known, reg_or_exec_v7347 instruction pc rs1 rs2 known, reg_or_exec_v7351 instruction pc rs1 rs2 known, reg_or_exec_v7355 instruction pc rs1 rs2 known, reg_or_exec_v7359 instruction pc rs1 rs2 known, reg_or_exec_v7363 instruction pc rs1 rs2 known, reg_or_exec_v7367 instruction pc rs1 rs2 known, reg_or_exec_v7371 instruction pc rs1 rs2 known, reg_or_exec_v7375 instruction pc rs1 rs2 known, reg_or_exec_v7379 instruction pc rs1 rs2 known, reg_or_exec_v7383 instruction pc rs1 rs2 known, reg_or_exec_v7387 instruction pc rs1 rs2 known, reg_or_exec_v7391 instruction pc rs1 rs2 known, reg_or_exec_v7395 instruction pc rs1 rs2 known, reg_or_exec_v7398 instruction pc rs1 rs2 known, reg_or_exec_v7401 instruction pc rs1 rs2 known, reg_or_exec_v7404 instruction pc rs1 rs2 known, reg_or_exec_v7407 instruction pc rs1 rs2 known, reg_or_exec_v7410 instruction pc rs1 rs2 known, reg_or_exec_v7413 instruction pc rs1 rs2 known, reg_or_exec_v7416 instruction pc rs1 rs2 known, reg_or_exec_v7419 instruction pc rs1 rs2 known, reg_or_exec_v7422 instruction pc rs1 rs2 known, reg_or_exec_v7425 instruction pc rs1 rs2 known, reg_or_exec_v7428 instruction pc rs1 rs2 known, reg_or_exec_v7431 instruction pc rs1 rs2 known, exec_v7788, exec_v7802, exec_v7803, exec_v7804, exec_v7805, exec_v7806, exec_v7807, exec_v7808, exec_v7809, exec_v7810, exec_v7811, exec_v7812, exec_v7813, exec_v7814, exec_v7815, exec_v7816, exec_v7817, exec_v7818, exec_v7819, exec_v7820, exec_v7821, exec_v7822, exec_v7823, exec_v7824, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7849, exec_v7850, exec_v7851, exec_v7852, exec_v7853, exec_v7854, exec_v7855, exec_v7856, exec_v7857, exec_v7858, exec_v7859, exec_v7860, exec_v7861, exec_v7862, exec_v7863, exec_v7864, exec_v7865, exec_v7866, exec_v7867, exec_v7868, exec_v7869, exec_v7870, exec_v7871, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7893, exec_v7894, exec_v7895, exec_v7896, exec_v7897, exec_v7898, exec_v7899, exec_v7900, exec_v7901, exec_v7902, exec_v7903, exec_v7904, exec_v7905, exec_v7906, exec_v7907, exec_v7908, exec_v7909, exec_v7910, exec_v7911, exec_v7912, exec_v7913, exec_v7914, exec_v7915, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v8033, exec_v8034]
#print axioms decoded_execution_or
theorem writeback_execution_or (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = ((writebackRs1 s) ||| (writebackRs2 s)) :=
  aligned.trans (decoded_execution_or _ _ _ _ known)
#print axioms writeback_execution_or
private theorem reg_and_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 28723 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 28723 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 28723 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 28723 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 28723 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 28723 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 28723 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 28723 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 28723 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 28723 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7343 instruction pc rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 28723 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7347 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7347 instruction pc rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 28723 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7351 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7351 instruction pc rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 28723 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7355 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7355 instruction pc rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 28723 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7359 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7359 instruction pc rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 28723 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7363 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7363 instruction pc rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 28723 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7367 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7367 instruction pc rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 28723 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7371 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7371 instruction pc rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 28723 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7375 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7375 instruction pc rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 28723 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7379 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7379 instruction pc rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 28723 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7383 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7383 instruction pc rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 28723 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7387 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7387 instruction pc rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 28723 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7391 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7391 instruction pc rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 28723 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7395 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7395 instruction pc rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 28723 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7398 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7398 instruction pc rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 28723 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7401 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7401 instruction pc rs1 rs2 = 0 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20499 :=
    mask_incompatible instruction 4261441663 28723 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7404 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7404 instruction pc rs1 rs2 = 0 := by
  change (if (1073762323 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762323 :=
    mask_incompatible instruction 4261441663 28723 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7407 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7407 instruction pc rs1 rs2 = 0 := by
  change (if (51 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 51 :=
    mask_incompatible instruction 4261441663 28723 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7410 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7410 instruction pc rs1 rs2 = 0 := by
  change (if (1073741875 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073741875 :=
    mask_incompatible instruction 4261441663 28723 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7413 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7413 instruction pc rs1 rs2 = 0 := by
  change (if (4147 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4147 :=
    mask_incompatible instruction 4261441663 28723 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7416 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7416 instruction pc rs1 rs2 = 0 := by
  change (if (8243 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 8243 :=
    mask_incompatible instruction 4261441663 28723 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7419 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7419 instruction pc rs1 rs2 = 0 := by
  change (if (12339 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 12339 :=
    mask_incompatible instruction 4261441663 28723 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7422 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7422 instruction pc rs1 rs2 = 0 := by
  change (if (16435 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 16435 :=
    mask_incompatible instruction 4261441663 28723 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7425 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7425 instruction pc rs1 rs2 = 0 := by
  change (if (20531 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20531 :=
    mask_incompatible instruction 4261441663 28723 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7428 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7428 instruction pc rs1 rs2 = 0 := by
  change (if (1073762355 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762355 :=
    mask_incompatible instruction 4261441663 28723 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7431 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7431 instruction pc rs1 rs2 = 0 := by
  change (if (24627 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 24627 :=
    mask_incompatible instruction 4261441663 28723 4261441663 24627 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_exec_v7434 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : exec_v7434 instruction pc rs1 rs2 = 1 := by
  change (if (28723 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 28723 :=
    mask_refines instruction 4261441663 28723 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_and (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) :
    decodedExecution instruction pc rs1 rs2 = (rs1 &&& rs2) := by
  simp [decodedExecution, aluSpec, exec_v512, reg_and_exec_v7303 instruction pc rs1 rs2 known, reg_and_exec_v7307 instruction pc rs1 rs2 known, reg_and_exec_v7311 instruction pc rs1 rs2 known, reg_and_exec_v7315 instruction pc rs1 rs2 known, reg_and_exec_v7319 instruction pc rs1 rs2 known, reg_and_exec_v7323 instruction pc rs1 rs2 known, reg_and_exec_v7327 instruction pc rs1 rs2 known, reg_and_exec_v7331 instruction pc rs1 rs2 known, reg_and_exec_v7335 instruction pc rs1 rs2 known, reg_and_exec_v7339 instruction pc rs1 rs2 known, reg_and_exec_v7343 instruction pc rs1 rs2 known, reg_and_exec_v7347 instruction pc rs1 rs2 known, reg_and_exec_v7351 instruction pc rs1 rs2 known, reg_and_exec_v7355 instruction pc rs1 rs2 known, reg_and_exec_v7359 instruction pc rs1 rs2 known, reg_and_exec_v7363 instruction pc rs1 rs2 known, reg_and_exec_v7367 instruction pc rs1 rs2 known, reg_and_exec_v7371 instruction pc rs1 rs2 known, reg_and_exec_v7375 instruction pc rs1 rs2 known, reg_and_exec_v7379 instruction pc rs1 rs2 known, reg_and_exec_v7383 instruction pc rs1 rs2 known, reg_and_exec_v7387 instruction pc rs1 rs2 known, reg_and_exec_v7391 instruction pc rs1 rs2 known, reg_and_exec_v7395 instruction pc rs1 rs2 known, reg_and_exec_v7398 instruction pc rs1 rs2 known, reg_and_exec_v7401 instruction pc rs1 rs2 known, reg_and_exec_v7404 instruction pc rs1 rs2 known, reg_and_exec_v7407 instruction pc rs1 rs2 known, reg_and_exec_v7410 instruction pc rs1 rs2 known, reg_and_exec_v7413 instruction pc rs1 rs2 known, reg_and_exec_v7416 instruction pc rs1 rs2 known, reg_and_exec_v7419 instruction pc rs1 rs2 known, reg_and_exec_v7422 instruction pc rs1 rs2 known, reg_and_exec_v7425 instruction pc rs1 rs2 known, reg_and_exec_v7428 instruction pc rs1 rs2 known, reg_and_exec_v7431 instruction pc rs1 rs2 known, reg_and_exec_v7434 instruction pc rs1 rs2 known, exec_v7789, exec_v7801, exec_v7802, exec_v7803, exec_v7804, exec_v7805, exec_v7806, exec_v7807, exec_v7808, exec_v7809, exec_v7810, exec_v7811, exec_v7812, exec_v7813, exec_v7814, exec_v7815, exec_v7816, exec_v7817, exec_v7818, exec_v7819, exec_v7820, exec_v7821, exec_v7822, exec_v7823, exec_v7824, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7848, exec_v7849, exec_v7850, exec_v7851, exec_v7852, exec_v7853, exec_v7854, exec_v7855, exec_v7856, exec_v7857, exec_v7858, exec_v7859, exec_v7860, exec_v7861, exec_v7862, exec_v7863, exec_v7864, exec_v7865, exec_v7866, exec_v7867, exec_v7868, exec_v7869, exec_v7870, exec_v7871, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7893, exec_v7894, exec_v7895, exec_v7896, exec_v7897, exec_v7898, exec_v7899, exec_v7900, exec_v7901, exec_v7902, exec_v7903, exec_v7904, exec_v7905, exec_v7906, exec_v7907, exec_v7908, exec_v7909, exec_v7910, exec_v7911, exec_v7912, exec_v7913, exec_v7914, exec_v7915, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v8033, exec_v8034]
#print axioms decoded_execution_and
theorem writeback_execution_and (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = ((writebackRs1 s) &&& (writebackRs2 s)) :=
  aligned.trans (decoded_execution_and _ _ _ _ known)
#print axioms writeback_execution_and
end RiscvMiniProofs
