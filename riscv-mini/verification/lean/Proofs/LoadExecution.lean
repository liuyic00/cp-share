import Proofs.RegisterExecution
import Proofs.ImmediateFacts
import Proofs.MaskFacts
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
private theorem reg_lb_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 3 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lb_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 3 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lb_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 3 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lb_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 3 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lb_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 3 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lb_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 3 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lb_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 3 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lb_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 3 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lb_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 3 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lb_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 3 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lb_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) : exec_v7343 instruction pc rs1 rs2 = 1 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 3 :=
    mask_refines instruction 28799 3 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_lb (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) :
    decodedExecution instruction pc rs1 rs2 = (rs1 + immediateI instruction) := by
  simp only [decodedExecution, exec_v200, exec_v22, exec_v26, exec_v29, exec_v4, exec_v512, exec_v716, exec_v725, reg_lb_exec_v7303 instruction pc rs1 rs2 known, reg_lb_exec_v7307 instruction pc rs1 rs2 known, reg_lb_exec_v7311 instruction pc rs1 rs2 known, reg_lb_exec_v7315 instruction pc rs1 rs2 known, reg_lb_exec_v7319 instruction pc rs1 rs2 known, reg_lb_exec_v7323 instruction pc rs1 rs2 known, reg_lb_exec_v7327 instruction pc rs1 rs2 known, reg_lb_exec_v7331 instruction pc rs1 rs2 known, reg_lb_exec_v7335 instruction pc rs1 rs2 known, reg_lb_exec_v7339 instruction pc rs1 rs2 known, reg_lb_exec_v7343 instruction pc rs1 rs2 known, exec_v7521, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7966, exec_v7967, exec_v7968, exec_v7969, exec_v7970, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8013, exec_v8017, exec_v8018, exec_v8021, exec_v8022, exec_v8023, exec_v8024, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
  rw [dut_immediate_form instruction]
  simp [aluSpec, immediateI_low5]
#print axioms decoded_execution_lb
theorem decoded_alu_op_lb (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) : exec_v7840 instruction pc rs1 rs2 = 0 := by
  simp only [exec_v200, exec_v22, exec_v26, exec_v29, exec_v4, exec_v512, exec_v716, exec_v725, reg_lb_exec_v7303 instruction pc rs1 rs2 known, reg_lb_exec_v7307 instruction pc rs1 rs2 known, reg_lb_exec_v7311 instruction pc rs1 rs2 known, reg_lb_exec_v7315 instruction pc rs1 rs2 known, reg_lb_exec_v7319 instruction pc rs1 rs2 known, reg_lb_exec_v7323 instruction pc rs1 rs2 known, reg_lb_exec_v7327 instruction pc rs1 rs2 known, reg_lb_exec_v7331 instruction pc rs1 rs2 known, reg_lb_exec_v7335 instruction pc rs1 rs2 known, reg_lb_exec_v7339 instruction pc rs1 rs2 known, reg_lb_exec_v7343 instruction pc rs1 rs2 known, exec_v7521, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7966, exec_v7967, exec_v7968, exec_v7969, exec_v7970, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8013, exec_v8017, exec_v8018, exec_v8021, exec_v8022, exec_v8023, exec_v8024, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
#print axioms decoded_alu_op_lb
theorem writeback_execution_lb (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = ((writebackRs1 s) + immediateI s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) :=
  aligned.trans (decoded_execution_lb _ _ _ _ known)
#print axioms writeback_execution_lb
private theorem reg_lh_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 4099 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lh_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 4099 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lh_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 4099 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lh_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 4099 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lh_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 4099 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lh_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 4099 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lh_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 4099 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lh_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 4099 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lh_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 4099 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lh_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 4099 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lh_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : exec_v7343 instruction pc rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 28799 4099 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lh_exec_v7347 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : exec_v7347 instruction pc rs1 rs2 = 1 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 4099 :=
    mask_refines instruction 28799 4099 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_lh (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) :
    decodedExecution instruction pc rs1 rs2 = (rs1 + immediateI instruction) := by
  simp only [decodedExecution, exec_v200, exec_v22, exec_v26, exec_v29, exec_v4, exec_v512, exec_v716, exec_v725, reg_lh_exec_v7303 instruction pc rs1 rs2 known, reg_lh_exec_v7307 instruction pc rs1 rs2 known, reg_lh_exec_v7311 instruction pc rs1 rs2 known, reg_lh_exec_v7315 instruction pc rs1 rs2 known, reg_lh_exec_v7319 instruction pc rs1 rs2 known, reg_lh_exec_v7323 instruction pc rs1 rs2 known, reg_lh_exec_v7327 instruction pc rs1 rs2 known, reg_lh_exec_v7331 instruction pc rs1 rs2 known, reg_lh_exec_v7335 instruction pc rs1 rs2 known, reg_lh_exec_v7339 instruction pc rs1 rs2 known, reg_lh_exec_v7343 instruction pc rs1 rs2 known, reg_lh_exec_v7347 instruction pc rs1 rs2 known, exec_v7521, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7965, exec_v7966, exec_v7967, exec_v7968, exec_v7969, exec_v7970, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8013, exec_v8017, exec_v8018, exec_v8021, exec_v8022, exec_v8023, exec_v8024, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
  rw [dut_immediate_form instruction]
  simp [aluSpec, immediateI_low5]
#print axioms decoded_execution_lh
theorem decoded_alu_op_lh (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : exec_v7840 instruction pc rs1 rs2 = 0 := by
  simp only [exec_v200, exec_v22, exec_v26, exec_v29, exec_v4, exec_v512, exec_v716, exec_v725, reg_lh_exec_v7303 instruction pc rs1 rs2 known, reg_lh_exec_v7307 instruction pc rs1 rs2 known, reg_lh_exec_v7311 instruction pc rs1 rs2 known, reg_lh_exec_v7315 instruction pc rs1 rs2 known, reg_lh_exec_v7319 instruction pc rs1 rs2 known, reg_lh_exec_v7323 instruction pc rs1 rs2 known, reg_lh_exec_v7327 instruction pc rs1 rs2 known, reg_lh_exec_v7331 instruction pc rs1 rs2 known, reg_lh_exec_v7335 instruction pc rs1 rs2 known, reg_lh_exec_v7339 instruction pc rs1 rs2 known, reg_lh_exec_v7343 instruction pc rs1 rs2 known, reg_lh_exec_v7347 instruction pc rs1 rs2 known, exec_v7521, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7965, exec_v7966, exec_v7967, exec_v7968, exec_v7969, exec_v7970, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8013, exec_v8017, exec_v8018, exec_v8021, exec_v8022, exec_v8023, exec_v8024, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
#print axioms decoded_alu_op_lh
theorem writeback_execution_lh (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = ((writebackRs1 s) + immediateI s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) :=
  aligned.trans (decoded_execution_lh _ _ _ _ known)
#print axioms writeback_execution_lh
private theorem reg_lw_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 8195 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 8195 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 8195 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 8195 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 8195 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 8195 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 8195 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 8195 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 8195 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 8195 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : exec_v7343 instruction pc rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 28799 8195 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_exec_v7347 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : exec_v7347 instruction pc rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 28799 8195 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_exec_v7351 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : exec_v7351 instruction pc rs1 rs2 = 1 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 8195 :=
    mask_refines instruction 28799 8195 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_lw (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) :
    decodedExecution instruction pc rs1 rs2 = (rs1 + immediateI instruction) := by
  simp only [decodedExecution, exec_v200, exec_v22, exec_v26, exec_v29, exec_v4, exec_v512, exec_v716, exec_v725, reg_lw_exec_v7303 instruction pc rs1 rs2 known, reg_lw_exec_v7307 instruction pc rs1 rs2 known, reg_lw_exec_v7311 instruction pc rs1 rs2 known, reg_lw_exec_v7315 instruction pc rs1 rs2 known, reg_lw_exec_v7319 instruction pc rs1 rs2 known, reg_lw_exec_v7323 instruction pc rs1 rs2 known, reg_lw_exec_v7327 instruction pc rs1 rs2 known, reg_lw_exec_v7331 instruction pc rs1 rs2 known, reg_lw_exec_v7335 instruction pc rs1 rs2 known, reg_lw_exec_v7339 instruction pc rs1 rs2 known, reg_lw_exec_v7343 instruction pc rs1 rs2 known, reg_lw_exec_v7347 instruction pc rs1 rs2 known, reg_lw_exec_v7351 instruction pc rs1 rs2 known, exec_v7521, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7964, exec_v7965, exec_v7966, exec_v7967, exec_v7968, exec_v7969, exec_v7970, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8013, exec_v8017, exec_v8018, exec_v8021, exec_v8022, exec_v8023, exec_v8024, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
  rw [dut_immediate_form instruction]
  simp [aluSpec, immediateI_low5]
#print axioms decoded_execution_lw
theorem decoded_alu_op_lw (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : exec_v7840 instruction pc rs1 rs2 = 0 := by
  simp only [exec_v200, exec_v22, exec_v26, exec_v29, exec_v4, exec_v512, exec_v716, exec_v725, reg_lw_exec_v7303 instruction pc rs1 rs2 known, reg_lw_exec_v7307 instruction pc rs1 rs2 known, reg_lw_exec_v7311 instruction pc rs1 rs2 known, reg_lw_exec_v7315 instruction pc rs1 rs2 known, reg_lw_exec_v7319 instruction pc rs1 rs2 known, reg_lw_exec_v7323 instruction pc rs1 rs2 known, reg_lw_exec_v7327 instruction pc rs1 rs2 known, reg_lw_exec_v7331 instruction pc rs1 rs2 known, reg_lw_exec_v7335 instruction pc rs1 rs2 known, reg_lw_exec_v7339 instruction pc rs1 rs2 known, reg_lw_exec_v7343 instruction pc rs1 rs2 known, reg_lw_exec_v7347 instruction pc rs1 rs2 known, reg_lw_exec_v7351 instruction pc rs1 rs2 known, exec_v7521, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7964, exec_v7965, exec_v7966, exec_v7967, exec_v7968, exec_v7969, exec_v7970, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8013, exec_v8017, exec_v8018, exec_v8021, exec_v8022, exec_v8023, exec_v8024, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
#print axioms decoded_alu_op_lw
theorem writeback_execution_lw (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = ((writebackRs1 s) + immediateI s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) :=
  aligned.trans (decoded_execution_lw _ _ _ _ known)
#print axioms writeback_execution_lw
private theorem reg_lbu_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 16387 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 16387 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 16387 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 16387 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 16387 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 16387 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 16387 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 16387 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 16387 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 16387 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : exec_v7343 instruction pc rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 28799 16387 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_exec_v7347 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : exec_v7347 instruction pc rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 28799 16387 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_exec_v7351 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : exec_v7351 instruction pc rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 28799 16387 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_exec_v7355 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : exec_v7355 instruction pc rs1 rs2 = 1 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 16387 :=
    mask_refines instruction 28799 16387 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_lbu (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) :
    decodedExecution instruction pc rs1 rs2 = (rs1 + immediateI instruction) := by
  simp only [decodedExecution, exec_v200, exec_v22, exec_v26, exec_v29, exec_v4, exec_v512, exec_v716, exec_v725, reg_lbu_exec_v7303 instruction pc rs1 rs2 known, reg_lbu_exec_v7307 instruction pc rs1 rs2 known, reg_lbu_exec_v7311 instruction pc rs1 rs2 known, reg_lbu_exec_v7315 instruction pc rs1 rs2 known, reg_lbu_exec_v7319 instruction pc rs1 rs2 known, reg_lbu_exec_v7323 instruction pc rs1 rs2 known, reg_lbu_exec_v7327 instruction pc rs1 rs2 known, reg_lbu_exec_v7331 instruction pc rs1 rs2 known, reg_lbu_exec_v7335 instruction pc rs1 rs2 known, reg_lbu_exec_v7339 instruction pc rs1 rs2 known, reg_lbu_exec_v7343 instruction pc rs1 rs2 known, reg_lbu_exec_v7347 instruction pc rs1 rs2 known, reg_lbu_exec_v7351 instruction pc rs1 rs2 known, reg_lbu_exec_v7355 instruction pc rs1 rs2 known, exec_v7521, exec_v7824, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7871, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7915, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7963, exec_v7964, exec_v7965, exec_v7966, exec_v7967, exec_v7968, exec_v7969, exec_v7970, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8013, exec_v8017, exec_v8018, exec_v8021, exec_v8022, exec_v8023, exec_v8024, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
  rw [dut_immediate_form instruction]
  simp [aluSpec, immediateI_low5]
#print axioms decoded_execution_lbu
theorem decoded_alu_op_lbu (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : exec_v7840 instruction pc rs1 rs2 = 0 := by
  simp only [exec_v200, exec_v22, exec_v26, exec_v29, exec_v4, exec_v512, exec_v716, exec_v725, reg_lbu_exec_v7303 instruction pc rs1 rs2 known, reg_lbu_exec_v7307 instruction pc rs1 rs2 known, reg_lbu_exec_v7311 instruction pc rs1 rs2 known, reg_lbu_exec_v7315 instruction pc rs1 rs2 known, reg_lbu_exec_v7319 instruction pc rs1 rs2 known, reg_lbu_exec_v7323 instruction pc rs1 rs2 known, reg_lbu_exec_v7327 instruction pc rs1 rs2 known, reg_lbu_exec_v7331 instruction pc rs1 rs2 known, reg_lbu_exec_v7335 instruction pc rs1 rs2 known, reg_lbu_exec_v7339 instruction pc rs1 rs2 known, reg_lbu_exec_v7343 instruction pc rs1 rs2 known, reg_lbu_exec_v7347 instruction pc rs1 rs2 known, reg_lbu_exec_v7351 instruction pc rs1 rs2 known, reg_lbu_exec_v7355 instruction pc rs1 rs2 known, exec_v7521, exec_v7824, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7871, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7915, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7963, exec_v7964, exec_v7965, exec_v7966, exec_v7967, exec_v7968, exec_v7969, exec_v7970, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8013, exec_v8017, exec_v8018, exec_v8021, exec_v8022, exec_v8023, exec_v8024, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
#print axioms decoded_alu_op_lbu
theorem writeback_execution_lbu (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = ((writebackRs1 s) + immediateI s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) :=
  aligned.trans (decoded_execution_lbu _ _ _ _ known)
#print axioms writeback_execution_lbu
private theorem reg_lhu_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 20483 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 20483 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 20483 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 20483 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 20483 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 20483 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 20483 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 20483 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 20483 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : exec_v7339 instruction pc rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 20483 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_exec_v7343 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : exec_v7343 instruction pc rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 28799 20483 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_exec_v7347 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : exec_v7347 instruction pc rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 28799 20483 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_exec_v7351 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : exec_v7351 instruction pc rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 28799 20483 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_exec_v7355 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : exec_v7355 instruction pc rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 28799 20483 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_exec_v7359 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : exec_v7359 instruction pc rs1 rs2 = 1 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 20483 :=
    mask_refines instruction 28799 20483 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_lhu (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) :
    decodedExecution instruction pc rs1 rs2 = (rs1 + immediateI instruction) := by
  simp only [decodedExecution, exec_v200, exec_v22, exec_v26, exec_v29, exec_v4, exec_v512, exec_v716, exec_v725, reg_lhu_exec_v7303 instruction pc rs1 rs2 known, reg_lhu_exec_v7307 instruction pc rs1 rs2 known, reg_lhu_exec_v7311 instruction pc rs1 rs2 known, reg_lhu_exec_v7315 instruction pc rs1 rs2 known, reg_lhu_exec_v7319 instruction pc rs1 rs2 known, reg_lhu_exec_v7323 instruction pc rs1 rs2 known, reg_lhu_exec_v7327 instruction pc rs1 rs2 known, reg_lhu_exec_v7331 instruction pc rs1 rs2 known, reg_lhu_exec_v7335 instruction pc rs1 rs2 known, reg_lhu_exec_v7339 instruction pc rs1 rs2 known, reg_lhu_exec_v7343 instruction pc rs1 rs2 known, reg_lhu_exec_v7347 instruction pc rs1 rs2 known, reg_lhu_exec_v7351 instruction pc rs1 rs2 known, reg_lhu_exec_v7355 instruction pc rs1 rs2 known, reg_lhu_exec_v7359 instruction pc rs1 rs2 known, exec_v7521, exec_v7823, exec_v7824, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7870, exec_v7871, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7914, exec_v7915, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7962, exec_v7963, exec_v7964, exec_v7965, exec_v7966, exec_v7967, exec_v7968, exec_v7969, exec_v7970, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8013, exec_v8017, exec_v8018, exec_v8021, exec_v8022, exec_v8023, exec_v8024, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
  rw [dut_immediate_form instruction]
  simp [aluSpec, immediateI_low5]
#print axioms decoded_execution_lhu
theorem decoded_alu_op_lhu (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : exec_v7840 instruction pc rs1 rs2 = 0 := by
  simp only [exec_v200, exec_v22, exec_v26, exec_v29, exec_v4, exec_v512, exec_v716, exec_v725, reg_lhu_exec_v7303 instruction pc rs1 rs2 known, reg_lhu_exec_v7307 instruction pc rs1 rs2 known, reg_lhu_exec_v7311 instruction pc rs1 rs2 known, reg_lhu_exec_v7315 instruction pc rs1 rs2 known, reg_lhu_exec_v7319 instruction pc rs1 rs2 known, reg_lhu_exec_v7323 instruction pc rs1 rs2 known, reg_lhu_exec_v7327 instruction pc rs1 rs2 known, reg_lhu_exec_v7331 instruction pc rs1 rs2 known, reg_lhu_exec_v7335 instruction pc rs1 rs2 known, reg_lhu_exec_v7339 instruction pc rs1 rs2 known, reg_lhu_exec_v7343 instruction pc rs1 rs2 known, reg_lhu_exec_v7347 instruction pc rs1 rs2 known, reg_lhu_exec_v7351 instruction pc rs1 rs2 known, reg_lhu_exec_v7355 instruction pc rs1 rs2 known, reg_lhu_exec_v7359 instruction pc rs1 rs2 known, exec_v7521, exec_v7823, exec_v7824, exec_v7825, exec_v7826, exec_v7827, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7870, exec_v7871, exec_v7872, exec_v7873, exec_v7874, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7914, exec_v7915, exec_v7916, exec_v7917, exec_v7918, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7962, exec_v7963, exec_v7964, exec_v7965, exec_v7966, exec_v7967, exec_v7968, exec_v7969, exec_v7970, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8013, exec_v8017, exec_v8018, exec_v8021, exec_v8022, exec_v8023, exec_v8024, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
#print axioms decoded_alu_op_lhu
theorem writeback_execution_lhu (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = ((writebackRs1 s) + immediateI s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) :=
  aligned.trans (decoded_execution_lhu _ _ _ _ known)
#print axioms writeback_execution_lhu
end RiscvMiniProofs
