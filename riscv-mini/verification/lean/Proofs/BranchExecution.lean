import Proofs.RegisterExecution
import Proofs.BranchImmediate
import Proofs.MaskFacts
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
private theorem reg_beq_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 99) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 99 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_beq_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 99) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 99 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_beq_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 99) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 99 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_beq_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 99) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 99 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_beq_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 99) : exec_v7319 instruction pc rs1 rs2 = 1 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 99 :=
    mask_refines instruction 28799 99 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_beq (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 99) :
    decodedExecution instruction pc rs1 rs2 = (pc + immediateB instruction) := by
  simp only [decodedExecution, exec_v200, exec_v22, exec_v4, exec_v512, exec_v716, exec_v725, reg_beq_exec_v7303 instruction pc rs1 rs2 known, reg_beq_exec_v7307 instruction pc rs1 rs2 known, reg_beq_exec_v7311 instruction pc rs1 rs2 known, reg_beq_exec_v7315 instruction pc rs1 rs2 known, reg_beq_exec_v7319 instruction pc rs1 rs2 known, exec_v7521, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8005, exec_v8006, exec_v8007, exec_v8008, exec_v8009, exec_v8010, exec_v8011, exec_v8012, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
  rw [branch_sign_replicate]
  rfl
#print axioms decoded_execution_beq
theorem writeback_execution_beq (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = (s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc + immediateB s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) :=
  aligned.trans (decoded_execution_beq _ _ _ _ known)
#print axioms writeback_execution_beq
private theorem reg_bne_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4195) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 4195 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bne_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4195) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 4195 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bne_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4195) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 4195 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bne_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4195) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 4195 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bne_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4195) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 4195 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bne_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4195) : exec_v7323 instruction pc rs1 rs2 = 1 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 4195 :=
    mask_refines instruction 28799 4195 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_bne (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4195) :
    decodedExecution instruction pc rs1 rs2 = (pc + immediateB instruction) := by
  simp only [decodedExecution, exec_v200, exec_v22, exec_v4, exec_v512, exec_v716, exec_v725, reg_bne_exec_v7303 instruction pc rs1 rs2 known, reg_bne_exec_v7307 instruction pc rs1 rs2 known, reg_bne_exec_v7311 instruction pc rs1 rs2 known, reg_bne_exec_v7315 instruction pc rs1 rs2 known, reg_bne_exec_v7319 instruction pc rs1 rs2 known, reg_bne_exec_v7323 instruction pc rs1 rs2 known, exec_v7521, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8005, exec_v8006, exec_v8007, exec_v8008, exec_v8009, exec_v8010, exec_v8011, exec_v8012, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
  rw [branch_sign_replicate]
  rfl
#print axioms decoded_execution_bne
theorem writeback_execution_bne (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = (s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc + immediateB s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) :=
  aligned.trans (decoded_execution_bne _ _ _ _ known)
#print axioms writeback_execution_bne
private theorem reg_blt_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16483) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 16483 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_blt_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16483) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 16483 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_blt_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16483) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 16483 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_blt_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16483) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 16483 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_blt_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16483) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 16483 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_blt_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16483) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 16483 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_blt_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16483) : exec_v7327 instruction pc rs1 rs2 = 1 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 16483 :=
    mask_refines instruction 28799 16483 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_blt (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16483) :
    decodedExecution instruction pc rs1 rs2 = (pc + immediateB instruction) := by
  simp only [decodedExecution, exec_v200, exec_v22, exec_v4, exec_v512, exec_v716, exec_v725, reg_blt_exec_v7303 instruction pc rs1 rs2 known, reg_blt_exec_v7307 instruction pc rs1 rs2 known, reg_blt_exec_v7311 instruction pc rs1 rs2 known, reg_blt_exec_v7315 instruction pc rs1 rs2 known, reg_blt_exec_v7319 instruction pc rs1 rs2 known, reg_blt_exec_v7323 instruction pc rs1 rs2 known, reg_blt_exec_v7327 instruction pc rs1 rs2 known, exec_v7521, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7970, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8005, exec_v8006, exec_v8007, exec_v8008, exec_v8009, exec_v8010, exec_v8011, exec_v8012, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
  rw [branch_sign_replicate]
  rfl
#print axioms decoded_execution_blt
theorem writeback_execution_blt (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = (s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc + immediateB s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) :=
  aligned.trans (decoded_execution_blt _ _ _ _ known)
#print axioms writeback_execution_blt
private theorem reg_bge_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20579) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 20579 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bge_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20579) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 20579 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bge_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20579) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 20579 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bge_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20579) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 20579 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bge_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20579) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 20579 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bge_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20579) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 20579 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bge_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20579) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 20579 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bge_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20579) : exec_v7331 instruction pc rs1 rs2 = 1 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 20579 :=
    mask_refines instruction 28799 20579 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_bge (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20579) :
    decodedExecution instruction pc rs1 rs2 = (pc + immediateB instruction) := by
  simp only [decodedExecution, exec_v200, exec_v22, exec_v4, exec_v512, exec_v716, exec_v725, reg_bge_exec_v7303 instruction pc rs1 rs2 known, reg_bge_exec_v7307 instruction pc rs1 rs2 known, reg_bge_exec_v7311 instruction pc rs1 rs2 known, reg_bge_exec_v7315 instruction pc rs1 rs2 known, reg_bge_exec_v7319 instruction pc rs1 rs2 known, reg_bge_exec_v7323 instruction pc rs1 rs2 known, reg_bge_exec_v7327 instruction pc rs1 rs2 known, reg_bge_exec_v7331 instruction pc rs1 rs2 known, exec_v7521, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7969, exec_v7970, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8005, exec_v8006, exec_v8007, exec_v8008, exec_v8009, exec_v8010, exec_v8011, exec_v8012, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
  rw [branch_sign_replicate]
  rfl
#print axioms decoded_execution_bge
theorem writeback_execution_bge (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = (s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc + immediateB s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) :=
  aligned.trans (decoded_execution_bge _ _ _ _ known)
#print axioms writeback_execution_bge
private theorem reg_bltu_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24675) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 24675 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bltu_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24675) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 24675 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bltu_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24675) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 24675 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bltu_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24675) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 24675 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bltu_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24675) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 24675 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bltu_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24675) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 24675 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bltu_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24675) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 24675 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bltu_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24675) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 24675 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bltu_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24675) : exec_v7335 instruction pc rs1 rs2 = 1 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 24675 :=
    mask_refines instruction 28799 24675 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_bltu (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24675) :
    decodedExecution instruction pc rs1 rs2 = (pc + immediateB instruction) := by
  simp only [decodedExecution, exec_v200, exec_v22, exec_v4, exec_v512, exec_v716, exec_v725, reg_bltu_exec_v7303 instruction pc rs1 rs2 known, reg_bltu_exec_v7307 instruction pc rs1 rs2 known, reg_bltu_exec_v7311 instruction pc rs1 rs2 known, reg_bltu_exec_v7315 instruction pc rs1 rs2 known, reg_bltu_exec_v7319 instruction pc rs1 rs2 known, reg_bltu_exec_v7323 instruction pc rs1 rs2 known, reg_bltu_exec_v7327 instruction pc rs1 rs2 known, reg_bltu_exec_v7331 instruction pc rs1 rs2 known, reg_bltu_exec_v7335 instruction pc rs1 rs2 known, exec_v7521, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7968, exec_v7969, exec_v7970, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8005, exec_v8006, exec_v8007, exec_v8008, exec_v8009, exec_v8010, exec_v8011, exec_v8012, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
  rw [branch_sign_replicate]
  rfl
#print axioms decoded_execution_bltu
theorem writeback_execution_bltu (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = (s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc + immediateB s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) :=
  aligned.trans (decoded_execution_bltu _ _ _ _ known)
#print axioms writeback_execution_bltu
private theorem reg_bgeu_exec_v7303 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28771) : exec_v7303 instruction pc rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 28771 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bgeu_exec_v7307 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28771) : exec_v7307 instruction pc rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 28771 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bgeu_exec_v7311 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28771) : exec_v7311 instruction pc rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 28771 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bgeu_exec_v7315 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28771) : exec_v7315 instruction pc rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 28771 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bgeu_exec_v7319 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28771) : exec_v7319 instruction pc rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 28771 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bgeu_exec_v7323 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28771) : exec_v7323 instruction pc rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 28771 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bgeu_exec_v7327 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28771) : exec_v7327 instruction pc rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 28771 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bgeu_exec_v7331 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28771) : exec_v7331 instruction pc rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 28771 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bgeu_exec_v7335 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28771) : exec_v7335 instruction pc rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 28771 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bgeu_exec_v7339 (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28771) : exec_v7339 instruction pc rs1 rs2 = 1 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 28771 :=
    mask_refines instruction 28799 28771 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_execution_bgeu (instruction pc rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28771) :
    decodedExecution instruction pc rs1 rs2 = (pc + immediateB instruction) := by
  simp only [decodedExecution, exec_v200, exec_v22, exec_v4, exec_v512, exec_v716, exec_v725, reg_bgeu_exec_v7303 instruction pc rs1 rs2 known, reg_bgeu_exec_v7307 instruction pc rs1 rs2 known, reg_bgeu_exec_v7311 instruction pc rs1 rs2 known, reg_bgeu_exec_v7315 instruction pc rs1 rs2 known, reg_bgeu_exec_v7319 instruction pc rs1 rs2 known, reg_bgeu_exec_v7323 instruction pc rs1 rs2 known, reg_bgeu_exec_v7327 instruction pc rs1 rs2 known, reg_bgeu_exec_v7331 instruction pc rs1 rs2 known, reg_bgeu_exec_v7335 instruction pc rs1 rs2 known, reg_bgeu_exec_v7339 instruction pc rs1 rs2 known, exec_v7521, exec_v7828, exec_v7829, exec_v7830, exec_v7831, exec_v7832, exec_v7833, exec_v7834, exec_v7835, exec_v7836, exec_v7837, exec_v7838, exec_v7839, exec_v7840, exec_v7875, exec_v7876, exec_v7877, exec_v7878, exec_v7879, exec_v7880, exec_v7881, exec_v7882, exec_v7883, exec_v7884, exec_v7885, exec_v7886, exec_v7887, exec_v7888, exec_v7889, exec_v7919, exec_v7920, exec_v7921, exec_v7922, exec_v7923, exec_v7924, exec_v7925, exec_v7926, exec_v7927, exec_v7928, exec_v7929, exec_v7930, exec_v7931, exec_v7967, exec_v7968, exec_v7969, exec_v7970, exec_v7971, exec_v7972, exec_v7973, exec_v7974, exec_v7975, exec_v7976, exec_v7977, exec_v7978, exec_v7979, exec_v7980, exec_v7981, exec_v7987, exec_v8001, exec_v8004, exec_v8005, exec_v8006, exec_v8007, exec_v8008, exec_v8009, exec_v8010, exec_v8011, exec_v8012, exec_v8025, exec_v8026, exec_v8027, exec_v8028, exec_v8029, exec_v8030, exec_v8031, exec_v8032, exec_v8033, exec_v8034, BitVec.reduceEq, ↓reduceIte]
  rw [branch_sign_replicate]
  rfl
#print axioms decoded_execution_bgeu
theorem writeback_execution_bgeu (s : State) (aligned : DecodedAluAligned s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = (s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc + immediateB s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) :=
  aligned.trans (decoded_execution_bgeu _ _ _ _ known)
#print axioms writeback_execution_bgeu
end RiscvMiniProofs
