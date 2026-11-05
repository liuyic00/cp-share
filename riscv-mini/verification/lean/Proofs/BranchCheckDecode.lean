import Proofs.PcCheckDecode
import Proofs.MaskFacts
namespace RiscvMiniProofs
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
private theorem reg_beq_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 99) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 99 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_beq_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 99) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 99 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_beq_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 99) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 99 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_beq_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 99) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 99 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_beq_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 99) : check_v7319 instruction rs1 rs2 = 1 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 99 :=
    mask_refines instruction 28799 99 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_beq (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 99) :
    decodedPcCheck instruction rs1 rs2 = (if check_v7730 instruction rs1 rs2 = 0 then 1 else 0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v29, check_v32, check_v4, check_v42, check_v716, reg_beq_check_v7303 instruction rs1 rs2 known, reg_beq_check_v7307 instruction rs1 rs2 known, reg_beq_check_v7311 instruction rs1 rs2 known, reg_beq_check_v7315 instruction rs1 rs2 known, reg_beq_check_v7319 instruction rs1 rs2 known, check_v7521, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
  exact BitVec.allOnes_and
#print axioms decoded_check_beq
private theorem reg_bne_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4195) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 4195 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bne_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4195) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 4195 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bne_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4195) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 4195 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bne_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4195) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 4195 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bne_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4195) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 4195 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bne_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4195) : check_v7323 instruction rs1 rs2 = 1 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 4195 :=
    mask_refines instruction 28799 4195 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_bne (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4195) :
    decodedPcCheck instruction rs1 rs2 = (check_v7730 instruction rs1 rs2) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v29, check_v32, check_v4, check_v42, check_v716, reg_bne_check_v7303 instruction rs1 rs2 known, reg_bne_check_v7307 instruction rs1 rs2 known, reg_bne_check_v7311 instruction rs1 rs2 known, reg_bne_check_v7315 instruction rs1 rs2 known, reg_bne_check_v7319 instruction rs1 rs2 known, reg_bne_check_v7323 instruction rs1 rs2 known, check_v7521, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
  exact BitVec.allOnes_and
#print axioms decoded_check_bne
private theorem reg_blt_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16483) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 16483 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_blt_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16483) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 16483 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_blt_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16483) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 16483 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_blt_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16483) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 16483 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_blt_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16483) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 16483 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_blt_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16483) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 16483 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_blt_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16483) : check_v7327 instruction rs1 rs2 = 1 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 16483 :=
    mask_refines instruction 28799 16483 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_blt (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16483) :
    decodedPcCheck instruction rs1 rs2 = (check_v7742 instruction rs1 rs2) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v29, check_v32, check_v4, check_v42, check_v716, reg_blt_check_v7303 instruction rs1 rs2 known, reg_blt_check_v7307 instruction rs1 rs2 known, reg_blt_check_v7311 instruction rs1 rs2 known, reg_blt_check_v7315 instruction rs1 rs2 known, reg_blt_check_v7319 instruction rs1 rs2 known, reg_blt_check_v7323 instruction rs1 rs2 known, reg_blt_check_v7327 instruction rs1 rs2 known, check_v7521, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
  exact BitVec.allOnes_and
#print axioms decoded_check_blt
private theorem reg_bge_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20579) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 20579 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bge_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20579) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 20579 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bge_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20579) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 20579 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bge_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20579) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 20579 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bge_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20579) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 20579 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bge_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20579) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 20579 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bge_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20579) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 20579 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bge_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20579) : check_v7331 instruction rs1 rs2 = 1 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 20579 :=
    mask_refines instruction 28799 20579 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_bge (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20579) :
    decodedPcCheck instruction rs1 rs2 = (if check_v7742 instruction rs1 rs2 = 0 then 1 else 0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v29, check_v32, check_v4, check_v42, check_v716, reg_bge_check_v7303 instruction rs1 rs2 known, reg_bge_check_v7307 instruction rs1 rs2 known, reg_bge_check_v7311 instruction rs1 rs2 known, reg_bge_check_v7315 instruction rs1 rs2 known, reg_bge_check_v7319 instruction rs1 rs2 known, reg_bge_check_v7323 instruction rs1 rs2 known, reg_bge_check_v7327 instruction rs1 rs2 known, reg_bge_check_v7331 instruction rs1 rs2 known, check_v7521, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
  exact BitVec.allOnes_and
#print axioms decoded_check_bge
private theorem reg_bltu_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24675) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 24675 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bltu_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24675) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 24675 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bltu_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24675) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 24675 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bltu_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24675) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 24675 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bltu_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24675) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 24675 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bltu_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24675) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 24675 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bltu_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24675) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 24675 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bltu_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24675) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 24675 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bltu_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24675) : check_v7335 instruction rs1 rs2 = 1 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 24675 :=
    mask_refines instruction 28799 24675 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_bltu (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24675) :
    decodedPcCheck instruction rs1 rs2 = (check_v7752 instruction rs1 rs2) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v29, check_v32, check_v4, check_v42, check_v716, reg_bltu_check_v7303 instruction rs1 rs2 known, reg_bltu_check_v7307 instruction rs1 rs2 known, reg_bltu_check_v7311 instruction rs1 rs2 known, reg_bltu_check_v7315 instruction rs1 rs2 known, reg_bltu_check_v7319 instruction rs1 rs2 known, reg_bltu_check_v7323 instruction rs1 rs2 known, reg_bltu_check_v7327 instruction rs1 rs2 known, reg_bltu_check_v7331 instruction rs1 rs2 known, reg_bltu_check_v7335 instruction rs1 rs2 known, check_v7521, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
  exact BitVec.allOnes_and
#print axioms decoded_check_bltu
private theorem reg_bgeu_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28771) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 28771 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bgeu_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28771) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 28771 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bgeu_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28771) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 28771 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bgeu_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28771) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 28771 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bgeu_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28771) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 28771 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bgeu_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28771) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 28771 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bgeu_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28771) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 28771 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bgeu_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28771) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 28771 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bgeu_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28771) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 28771 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_bgeu_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28771) : check_v7339 instruction rs1 rs2 = 1 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 28771 :=
    mask_refines instruction 28799 28771 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_bgeu (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28771) :
    decodedPcCheck instruction rs1 rs2 = (if check_v7752 instruction rs1 rs2 = 0 then 1 else 0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v29, check_v32, check_v4, check_v42, check_v716, reg_bgeu_check_v7303 instruction rs1 rs2 known, reg_bgeu_check_v7307 instruction rs1 rs2 known, reg_bgeu_check_v7311 instruction rs1 rs2 known, reg_bgeu_check_v7315 instruction rs1 rs2 known, reg_bgeu_check_v7319 instruction rs1 rs2 known, reg_bgeu_check_v7323 instruction rs1 rs2 known, reg_bgeu_check_v7327 instruction rs1 rs2 known, reg_bgeu_check_v7331 instruction rs1 rs2 known, reg_bgeu_check_v7335 instruction rs1 rs2 known, reg_bgeu_check_v7339 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
  exact BitVec.allOnes_and
#print axioms decoded_check_bgeu
end RiscvMiniProofs
