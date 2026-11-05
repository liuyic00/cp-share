import Proofs.PcCheckDecode
import Proofs.MaskFacts
namespace RiscvMiniProofs
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
private theorem reg_lui_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 127 = 55) : check_v7303 instruction rs1 rs2 = 1 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 1
  have yes : instruction &&& 127 = 55 :=
    mask_refines instruction 127 55 127 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_lui (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 127 = 55) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_lui_check_v7303 instruction rs1 rs2 known, check_v7521, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_lui
private theorem reg_auipc_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 127 = 23) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 127 23 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_auipc_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 127 = 23) : check_v7307 instruction rs1 rs2 = 1 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 1
  have yes : instruction &&& 127 = 23 :=
    mask_refines instruction 127 23 127 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_auipc (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 127 = 23) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_auipc_check_v7303 instruction rs1 rs2 known, reg_auipc_check_v7307 instruction rs1 rs2 known, check_v7521, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_auipc
private theorem reg_jal_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 127 = 111) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 127 111 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_jal_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 127 = 111) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 127 111 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_jal_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 127 = 111) : check_v7311 instruction rs1 rs2 = 1 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 1
  have yes : instruction &&& 127 = 111 :=
    mask_refines instruction 127 111 127 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_jal (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 127 = 111) :
    decodedPcCheck instruction rs1 rs2 = (1) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v4, check_v42, check_v716, reg_jal_check_v7303 instruction rs1 rs2 known, reg_jal_check_v7307 instruction rs1 rs2 known, reg_jal_check_v7311 instruction rs1 rs2 known, check_v7521, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_jal
private theorem reg_jalr_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 103) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 103 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_jalr_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 103) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 103 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_jalr_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 103) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 103 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_jalr_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 103) : check_v7315 instruction rs1 rs2 = 1 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 103 :=
    mask_refines instruction 28799 103 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_jalr (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 103) :
    decodedPcCheck instruction rs1 rs2 = (1) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v4, check_v42, check_v716, reg_jalr_check_v7303 instruction rs1 rs2 known, reg_jalr_check_v7307 instruction rs1 rs2 known, reg_jalr_check_v7311 instruction rs1 rs2 known, reg_jalr_check_v7315 instruction rs1 rs2 known, check_v7521, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_jalr
private theorem reg_lb_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 3 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lb_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 3 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lb_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 3 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lb_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 3 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lb_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 3 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lb_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 3 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lb_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 3 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lb_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 3 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lb_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 3 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lb_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 3 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lb_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) : check_v7343 instruction rs1 rs2 = 1 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 3 :=
    mask_refines instruction 28799 3 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_lb (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 3) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v38, check_v4, check_v42, check_v716, reg_lb_check_v7303 instruction rs1 rs2 known, reg_lb_check_v7307 instruction rs1 rs2 known, reg_lb_check_v7311 instruction rs1 rs2 known, reg_lb_check_v7315 instruction rs1 rs2 known, reg_lb_check_v7319 instruction rs1 rs2 known, reg_lb_check_v7323 instruction rs1 rs2 known, reg_lb_check_v7327 instruction rs1 rs2 known, reg_lb_check_v7331 instruction rs1 rs2 known, reg_lb_check_v7335 instruction rs1 rs2 known, reg_lb_check_v7339 instruction rs1 rs2 known, reg_lb_check_v7343 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_lb
private theorem reg_lh_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 4099 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lh_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 4099 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lh_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 4099 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lh_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 4099 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lh_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 4099 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lh_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 4099 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lh_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 4099 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lh_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 4099 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lh_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 4099 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lh_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 4099 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lh_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 28799 4099 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lh_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) : check_v7347 instruction rs1 rs2 = 1 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 4099 :=
    mask_refines instruction 28799 4099 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_lh (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4099) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v38, check_v4, check_v42, check_v716, reg_lh_check_v7303 instruction rs1 rs2 known, reg_lh_check_v7307 instruction rs1 rs2 known, reg_lh_check_v7311 instruction rs1 rs2 known, reg_lh_check_v7315 instruction rs1 rs2 known, reg_lh_check_v7319 instruction rs1 rs2 known, reg_lh_check_v7323 instruction rs1 rs2 known, reg_lh_check_v7327 instruction rs1 rs2 known, reg_lh_check_v7331 instruction rs1 rs2 known, reg_lh_check_v7335 instruction rs1 rs2 known, reg_lh_check_v7339 instruction rs1 rs2 known, reg_lh_check_v7343 instruction rs1 rs2 known, reg_lh_check_v7347 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_lh
private theorem reg_lw_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 8195 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 8195 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 8195 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 8195 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 8195 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 8195 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 8195 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 8195 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 8195 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 8195 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 28799 8195 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 28799 8195 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lw_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) : check_v7351 instruction rs1 rs2 = 1 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 8195 :=
    mask_refines instruction 28799 8195 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_lw (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8195) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v38, check_v4, check_v42, check_v716, reg_lw_check_v7303 instruction rs1 rs2 known, reg_lw_check_v7307 instruction rs1 rs2 known, reg_lw_check_v7311 instruction rs1 rs2 known, reg_lw_check_v7315 instruction rs1 rs2 known, reg_lw_check_v7319 instruction rs1 rs2 known, reg_lw_check_v7323 instruction rs1 rs2 known, reg_lw_check_v7327 instruction rs1 rs2 known, reg_lw_check_v7331 instruction rs1 rs2 known, reg_lw_check_v7335 instruction rs1 rs2 known, reg_lw_check_v7339 instruction rs1 rs2 known, reg_lw_check_v7343 instruction rs1 rs2 known, reg_lw_check_v7347 instruction rs1 rs2 known, reg_lw_check_v7351 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_lw
private theorem reg_lbu_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 16387 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 16387 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 16387 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 16387 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 16387 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 16387 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 16387 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 16387 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 16387 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 16387 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 28799 16387 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 28799 16387 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 28799 16387 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lbu_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) : check_v7355 instruction rs1 rs2 = 1 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 16387 :=
    mask_refines instruction 28799 16387 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_lbu (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16387) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v38, check_v4, check_v42, check_v716, reg_lbu_check_v7303 instruction rs1 rs2 known, reg_lbu_check_v7307 instruction rs1 rs2 known, reg_lbu_check_v7311 instruction rs1 rs2 known, reg_lbu_check_v7315 instruction rs1 rs2 known, reg_lbu_check_v7319 instruction rs1 rs2 known, reg_lbu_check_v7323 instruction rs1 rs2 known, reg_lbu_check_v7327 instruction rs1 rs2 known, reg_lbu_check_v7331 instruction rs1 rs2 known, reg_lbu_check_v7335 instruction rs1 rs2 known, reg_lbu_check_v7339 instruction rs1 rs2 known, reg_lbu_check_v7343 instruction rs1 rs2 known, reg_lbu_check_v7347 instruction rs1 rs2 known, reg_lbu_check_v7351 instruction rs1 rs2 known, reg_lbu_check_v7355 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_lbu
private theorem reg_lhu_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 20483 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 20483 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 20483 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 20483 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 20483 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 20483 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 20483 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 20483 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 20483 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 20483 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 28799 20483 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 28799 20483 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 28799 20483 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : check_v7355 instruction rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 28799 20483 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_lhu_check_v7359 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) : check_v7359 instruction rs1 rs2 = 1 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 20483 :=
    mask_refines instruction 28799 20483 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_lhu (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 20483) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v38, check_v4, check_v42, check_v716, reg_lhu_check_v7303 instruction rs1 rs2 known, reg_lhu_check_v7307 instruction rs1 rs2 known, reg_lhu_check_v7311 instruction rs1 rs2 known, reg_lhu_check_v7315 instruction rs1 rs2 known, reg_lhu_check_v7319 instruction rs1 rs2 known, reg_lhu_check_v7323 instruction rs1 rs2 known, reg_lhu_check_v7327 instruction rs1 rs2 known, reg_lhu_check_v7331 instruction rs1 rs2 known, reg_lhu_check_v7335 instruction rs1 rs2 known, reg_lhu_check_v7339 instruction rs1 rs2 known, reg_lhu_check_v7343 instruction rs1 rs2 known, reg_lhu_check_v7347 instruction rs1 rs2 known, reg_lhu_check_v7351 instruction rs1 rs2 known, reg_lhu_check_v7355 instruction rs1 rs2 known, reg_lhu_check_v7359 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8457, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_lhu
private theorem reg_sb_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 35) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 35 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sb_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 35) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 35 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sb_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 35) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 35 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sb_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 35) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 35 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sb_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 35) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 35 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sb_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 35) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 35 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sb_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 35) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 35 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sb_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 35) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 35 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sb_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 35) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 35 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sb_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 35) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 35 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sb_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 35) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 28799 35 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sb_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 35) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 28799 35 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sb_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 35) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 28799 35 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sb_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 35) : check_v7355 instruction rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 28799 35 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sb_check_v7359 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 35) : check_v7359 instruction rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 28799 35 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sb_check_v7363 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 35) : check_v7363 instruction rs1 rs2 = 1 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 35 :=
    mask_refines instruction 28799 35 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_sb (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 35) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_sb_check_v7303 instruction rs1 rs2 known, reg_sb_check_v7307 instruction rs1 rs2 known, reg_sb_check_v7311 instruction rs1 rs2 known, reg_sb_check_v7315 instruction rs1 rs2 known, reg_sb_check_v7319 instruction rs1 rs2 known, reg_sb_check_v7323 instruction rs1 rs2 known, reg_sb_check_v7327 instruction rs1 rs2 known, reg_sb_check_v7331 instruction rs1 rs2 known, reg_sb_check_v7335 instruction rs1 rs2 known, reg_sb_check_v7339 instruction rs1 rs2 known, reg_sb_check_v7343 instruction rs1 rs2 known, reg_sb_check_v7347 instruction rs1 rs2 known, reg_sb_check_v7351 instruction rs1 rs2 known, reg_sb_check_v7355 instruction rs1 rs2 known, reg_sb_check_v7359 instruction rs1 rs2 known, reg_sb_check_v7363 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8456, check_v8457, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_sb
private theorem reg_sh_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4131) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 4131 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sh_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4131) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 4131 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sh_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4131) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 4131 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sh_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4131) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 4131 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sh_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4131) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 4131 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sh_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4131) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 4131 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sh_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4131) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 4131 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sh_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4131) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 4131 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sh_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4131) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 4131 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sh_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4131) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 4131 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sh_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4131) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 28799 4131 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sh_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4131) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 28799 4131 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sh_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4131) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 28799 4131 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sh_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4131) : check_v7355 instruction rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 28799 4131 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sh_check_v7359 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4131) : check_v7359 instruction rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 28799 4131 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sh_check_v7363 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4131) : check_v7363 instruction rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 28799 4131 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sh_check_v7367 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4131) : check_v7367 instruction rs1 rs2 = 1 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 4131 :=
    mask_refines instruction 28799 4131 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_sh (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 4131) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_sh_check_v7303 instruction rs1 rs2 known, reg_sh_check_v7307 instruction rs1 rs2 known, reg_sh_check_v7311 instruction rs1 rs2 known, reg_sh_check_v7315 instruction rs1 rs2 known, reg_sh_check_v7319 instruction rs1 rs2 known, reg_sh_check_v7323 instruction rs1 rs2 known, reg_sh_check_v7327 instruction rs1 rs2 known, reg_sh_check_v7331 instruction rs1 rs2 known, reg_sh_check_v7335 instruction rs1 rs2 known, reg_sh_check_v7339 instruction rs1 rs2 known, reg_sh_check_v7343 instruction rs1 rs2 known, reg_sh_check_v7347 instruction rs1 rs2 known, reg_sh_check_v7351 instruction rs1 rs2 known, reg_sh_check_v7355 instruction rs1 rs2 known, reg_sh_check_v7359 instruction rs1 rs2 known, reg_sh_check_v7363 instruction rs1 rs2 known, reg_sh_check_v7367 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8455, check_v8456, check_v8457, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_sh
private theorem reg_sw_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8227) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 8227 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sw_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8227) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 8227 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sw_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8227) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 8227 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sw_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8227) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 8227 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sw_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8227) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 8227 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sw_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8227) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 8227 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sw_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8227) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 8227 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sw_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8227) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 8227 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sw_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8227) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 8227 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sw_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8227) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 8227 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sw_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8227) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 28799 8227 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sw_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8227) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 28799 8227 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sw_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8227) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 28799 8227 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sw_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8227) : check_v7355 instruction rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 28799 8227 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sw_check_v7359 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8227) : check_v7359 instruction rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 28799 8227 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sw_check_v7363 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8227) : check_v7363 instruction rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 28799 8227 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sw_check_v7367 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8227) : check_v7367 instruction rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 28799 8227 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sw_check_v7371 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8227) : check_v7371 instruction rs1 rs2 = 1 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 8227 :=
    mask_refines instruction 28799 8227 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_sw (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8227) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_sw_check_v7303 instruction rs1 rs2 known, reg_sw_check_v7307 instruction rs1 rs2 known, reg_sw_check_v7311 instruction rs1 rs2 known, reg_sw_check_v7315 instruction rs1 rs2 known, reg_sw_check_v7319 instruction rs1 rs2 known, reg_sw_check_v7323 instruction rs1 rs2 known, reg_sw_check_v7327 instruction rs1 rs2 known, reg_sw_check_v7331 instruction rs1 rs2 known, reg_sw_check_v7335 instruction rs1 rs2 known, reg_sw_check_v7339 instruction rs1 rs2 known, reg_sw_check_v7343 instruction rs1 rs2 known, reg_sw_check_v7347 instruction rs1 rs2 known, reg_sw_check_v7351 instruction rs1 rs2 known, reg_sw_check_v7355 instruction rs1 rs2 known, reg_sw_check_v7359 instruction rs1 rs2 known, reg_sw_check_v7363 instruction rs1 rs2 known, reg_sw_check_v7367 instruction rs1 rs2 known, reg_sw_check_v7371 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8454, check_v8455, check_v8456, check_v8457, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_sw
private theorem reg_addi_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 19 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 19 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 19 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 19 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 19 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 19 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 19 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 19 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 19 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 19 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 28799 19 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 28799 19 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 28799 19 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : check_v7355 instruction rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 28799 19 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_check_v7359 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : check_v7359 instruction rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 28799 19 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_check_v7363 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : check_v7363 instruction rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 28799 19 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_check_v7367 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : check_v7367 instruction rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 28799 19 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_check_v7371 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : check_v7371 instruction rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 28799 19 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_addi_check_v7375 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) : check_v7375 instruction rs1 rs2 = 1 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 19 :=
    mask_refines instruction 28799 19 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_addi (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 19) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_addi_check_v7303 instruction rs1 rs2 known, reg_addi_check_v7307 instruction rs1 rs2 known, reg_addi_check_v7311 instruction rs1 rs2 known, reg_addi_check_v7315 instruction rs1 rs2 known, reg_addi_check_v7319 instruction rs1 rs2 known, reg_addi_check_v7323 instruction rs1 rs2 known, reg_addi_check_v7327 instruction rs1 rs2 known, reg_addi_check_v7331 instruction rs1 rs2 known, reg_addi_check_v7335 instruction rs1 rs2 known, reg_addi_check_v7339 instruction rs1 rs2 known, reg_addi_check_v7343 instruction rs1 rs2 known, reg_addi_check_v7347 instruction rs1 rs2 known, reg_addi_check_v7351 instruction rs1 rs2 known, reg_addi_check_v7355 instruction rs1 rs2 known, reg_addi_check_v7359 instruction rs1 rs2 known, reg_addi_check_v7363 instruction rs1 rs2 known, reg_addi_check_v7367 instruction rs1 rs2 known, reg_addi_check_v7371 instruction rs1 rs2 known, reg_addi_check_v7375 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8453, check_v8454, check_v8455, check_v8456, check_v8457, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_addi
private theorem reg_slti_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 8211 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 8211 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 8211 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 8211 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 8211 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 8211 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 8211 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 8211 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 8211 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 8211 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 28799 8211 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 28799 8211 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 28799 8211 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : check_v7355 instruction rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 28799 8211 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_check_v7359 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : check_v7359 instruction rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 28799 8211 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_check_v7363 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : check_v7363 instruction rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 28799 8211 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_check_v7367 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : check_v7367 instruction rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 28799 8211 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_check_v7371 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : check_v7371 instruction rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 28799 8211 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_check_v7375 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : check_v7375 instruction rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 28799 8211 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slti_check_v7379 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) : check_v7379 instruction rs1 rs2 = 1 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 8211 :=
    mask_refines instruction 28799 8211 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_slti (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 8211) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_slti_check_v7303 instruction rs1 rs2 known, reg_slti_check_v7307 instruction rs1 rs2 known, reg_slti_check_v7311 instruction rs1 rs2 known, reg_slti_check_v7315 instruction rs1 rs2 known, reg_slti_check_v7319 instruction rs1 rs2 known, reg_slti_check_v7323 instruction rs1 rs2 known, reg_slti_check_v7327 instruction rs1 rs2 known, reg_slti_check_v7331 instruction rs1 rs2 known, reg_slti_check_v7335 instruction rs1 rs2 known, reg_slti_check_v7339 instruction rs1 rs2 known, reg_slti_check_v7343 instruction rs1 rs2 known, reg_slti_check_v7347 instruction rs1 rs2 known, reg_slti_check_v7351 instruction rs1 rs2 known, reg_slti_check_v7355 instruction rs1 rs2 known, reg_slti_check_v7359 instruction rs1 rs2 known, reg_slti_check_v7363 instruction rs1 rs2 known, reg_slti_check_v7367 instruction rs1 rs2 known, reg_slti_check_v7371 instruction rs1 rs2 known, reg_slti_check_v7375 instruction rs1 rs2 known, reg_slti_check_v7379 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8452, check_v8453, check_v8454, check_v8455, check_v8456, check_v8457, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_slti
private theorem reg_sltiu_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 12307 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 12307 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 12307 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 12307 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 12307 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 12307 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 12307 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 12307 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 12307 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 12307 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 28799 12307 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 28799 12307 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 28799 12307 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : check_v7355 instruction rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 28799 12307 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_check_v7359 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : check_v7359 instruction rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 28799 12307 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_check_v7363 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : check_v7363 instruction rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 28799 12307 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_check_v7367 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : check_v7367 instruction rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 28799 12307 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_check_v7371 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : check_v7371 instruction rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 28799 12307 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_check_v7375 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : check_v7375 instruction rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 28799 12307 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_check_v7379 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : check_v7379 instruction rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 28799 12307 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltiu_check_v7383 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) : check_v7383 instruction rs1 rs2 = 1 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 12307 :=
    mask_refines instruction 28799 12307 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_sltiu (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 12307) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_sltiu_check_v7303 instruction rs1 rs2 known, reg_sltiu_check_v7307 instruction rs1 rs2 known, reg_sltiu_check_v7311 instruction rs1 rs2 known, reg_sltiu_check_v7315 instruction rs1 rs2 known, reg_sltiu_check_v7319 instruction rs1 rs2 known, reg_sltiu_check_v7323 instruction rs1 rs2 known, reg_sltiu_check_v7327 instruction rs1 rs2 known, reg_sltiu_check_v7331 instruction rs1 rs2 known, reg_sltiu_check_v7335 instruction rs1 rs2 known, reg_sltiu_check_v7339 instruction rs1 rs2 known, reg_sltiu_check_v7343 instruction rs1 rs2 known, reg_sltiu_check_v7347 instruction rs1 rs2 known, reg_sltiu_check_v7351 instruction rs1 rs2 known, reg_sltiu_check_v7355 instruction rs1 rs2 known, reg_sltiu_check_v7359 instruction rs1 rs2 known, reg_sltiu_check_v7363 instruction rs1 rs2 known, reg_sltiu_check_v7367 instruction rs1 rs2 known, reg_sltiu_check_v7371 instruction rs1 rs2 known, reg_sltiu_check_v7375 instruction rs1 rs2 known, reg_sltiu_check_v7379 instruction rs1 rs2 known, reg_sltiu_check_v7383 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8451, check_v8452, check_v8453, check_v8454, check_v8455, check_v8456, check_v8457, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_sltiu
private theorem reg_xori_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 16403 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 16403 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 16403 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 16403 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 16403 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 16403 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 16403 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 16403 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 16403 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 16403 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 28799 16403 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 28799 16403 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 28799 16403 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : check_v7355 instruction rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 28799 16403 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_check_v7359 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : check_v7359 instruction rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 28799 16403 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_check_v7363 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : check_v7363 instruction rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 28799 16403 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_check_v7367 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : check_v7367 instruction rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 28799 16403 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_check_v7371 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : check_v7371 instruction rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 28799 16403 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_check_v7375 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : check_v7375 instruction rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 28799 16403 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_check_v7379 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : check_v7379 instruction rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 28799 16403 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_check_v7383 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : check_v7383 instruction rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 28799 16403 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xori_check_v7387 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) : check_v7387 instruction rs1 rs2 = 1 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 16403 :=
    mask_refines instruction 28799 16403 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_xori (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 16403) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_xori_check_v7303 instruction rs1 rs2 known, reg_xori_check_v7307 instruction rs1 rs2 known, reg_xori_check_v7311 instruction rs1 rs2 known, reg_xori_check_v7315 instruction rs1 rs2 known, reg_xori_check_v7319 instruction rs1 rs2 known, reg_xori_check_v7323 instruction rs1 rs2 known, reg_xori_check_v7327 instruction rs1 rs2 known, reg_xori_check_v7331 instruction rs1 rs2 known, reg_xori_check_v7335 instruction rs1 rs2 known, reg_xori_check_v7339 instruction rs1 rs2 known, reg_xori_check_v7343 instruction rs1 rs2 known, reg_xori_check_v7347 instruction rs1 rs2 known, reg_xori_check_v7351 instruction rs1 rs2 known, reg_xori_check_v7355 instruction rs1 rs2 known, reg_xori_check_v7359 instruction rs1 rs2 known, reg_xori_check_v7363 instruction rs1 rs2 known, reg_xori_check_v7367 instruction rs1 rs2 known, reg_xori_check_v7371 instruction rs1 rs2 known, reg_xori_check_v7375 instruction rs1 rs2 known, reg_xori_check_v7379 instruction rs1 rs2 known, reg_xori_check_v7383 instruction rs1 rs2 known, reg_xori_check_v7387 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8450, check_v8451, check_v8452, check_v8453, check_v8454, check_v8455, check_v8456, check_v8457, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_xori
private theorem reg_ori_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 24595 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 24595 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 24595 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 24595 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 24595 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 24595 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 24595 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 24595 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 24595 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 24595 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 28799 24595 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 28799 24595 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 28799 24595 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : check_v7355 instruction rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 28799 24595 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_check_v7359 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : check_v7359 instruction rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 28799 24595 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_check_v7363 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : check_v7363 instruction rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 28799 24595 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_check_v7367 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : check_v7367 instruction rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 28799 24595 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_check_v7371 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : check_v7371 instruction rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 28799 24595 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_check_v7375 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : check_v7375 instruction rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 28799 24595 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_check_v7379 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : check_v7379 instruction rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 28799 24595 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_check_v7383 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : check_v7383 instruction rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 28799 24595 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_check_v7387 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : check_v7387 instruction rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 28799 24595 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_ori_check_v7391 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) : check_v7391 instruction rs1 rs2 = 1 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 24595 :=
    mask_refines instruction 28799 24595 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_ori (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 24595) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_ori_check_v7303 instruction rs1 rs2 known, reg_ori_check_v7307 instruction rs1 rs2 known, reg_ori_check_v7311 instruction rs1 rs2 known, reg_ori_check_v7315 instruction rs1 rs2 known, reg_ori_check_v7319 instruction rs1 rs2 known, reg_ori_check_v7323 instruction rs1 rs2 known, reg_ori_check_v7327 instruction rs1 rs2 known, reg_ori_check_v7331 instruction rs1 rs2 known, reg_ori_check_v7335 instruction rs1 rs2 known, reg_ori_check_v7339 instruction rs1 rs2 known, reg_ori_check_v7343 instruction rs1 rs2 known, reg_ori_check_v7347 instruction rs1 rs2 known, reg_ori_check_v7351 instruction rs1 rs2 known, reg_ori_check_v7355 instruction rs1 rs2 known, reg_ori_check_v7359 instruction rs1 rs2 known, reg_ori_check_v7363 instruction rs1 rs2 known, reg_ori_check_v7367 instruction rs1 rs2 known, reg_ori_check_v7371 instruction rs1 rs2 known, reg_ori_check_v7375 instruction rs1 rs2 known, reg_ori_check_v7379 instruction rs1 rs2 known, reg_ori_check_v7383 instruction rs1 rs2 known, reg_ori_check_v7387 instruction rs1 rs2 known, reg_ori_check_v7391 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8449, check_v8450, check_v8451, check_v8452, check_v8453, check_v8454, check_v8455, check_v8456, check_v8457, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_ori
private theorem reg_andi_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 28799 28691 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 28799 28691 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 28799 28691 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 28799 28691 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 28799 28691 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 28799 28691 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 28799 28691 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 28799 28691 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 28799 28691 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 28799 28691 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 28799 28691 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 28799 28691 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 28799 28691 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7355 instruction rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 28799 28691 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_check_v7359 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7359 instruction rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 28799 28691 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_check_v7363 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7363 instruction rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 28799 28691 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_check_v7367 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7367 instruction rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 28799 28691 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_check_v7371 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7371 instruction rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 28799 28691 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_check_v7375 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7375 instruction rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 28799 28691 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_check_v7379 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7379 instruction rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 28799 28691 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_check_v7383 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7383 instruction rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 28799 28691 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_check_v7387 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7387 instruction rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 28799 28691 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_check_v7391 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7391 instruction rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 28799 28691 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_andi_check_v7395 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) : check_v7395 instruction rs1 rs2 = 1 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 1
  have yes : instruction &&& 28799 = 28691 :=
    mask_refines instruction 28799 28691 28799 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_andi (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 28799 = 28691) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_andi_check_v7303 instruction rs1 rs2 known, reg_andi_check_v7307 instruction rs1 rs2 known, reg_andi_check_v7311 instruction rs1 rs2 known, reg_andi_check_v7315 instruction rs1 rs2 known, reg_andi_check_v7319 instruction rs1 rs2 known, reg_andi_check_v7323 instruction rs1 rs2 known, reg_andi_check_v7327 instruction rs1 rs2 known, reg_andi_check_v7331 instruction rs1 rs2 known, reg_andi_check_v7335 instruction rs1 rs2 known, reg_andi_check_v7339 instruction rs1 rs2 known, reg_andi_check_v7343 instruction rs1 rs2 known, reg_andi_check_v7347 instruction rs1 rs2 known, reg_andi_check_v7351 instruction rs1 rs2 known, reg_andi_check_v7355 instruction rs1 rs2 known, reg_andi_check_v7359 instruction rs1 rs2 known, reg_andi_check_v7363 instruction rs1 rs2 known, reg_andi_check_v7367 instruction rs1 rs2 known, reg_andi_check_v7371 instruction rs1 rs2 known, reg_andi_check_v7375 instruction rs1 rs2 known, reg_andi_check_v7379 instruction rs1 rs2 known, reg_andi_check_v7383 instruction rs1 rs2 known, reg_andi_check_v7387 instruction rs1 rs2 known, reg_andi_check_v7391 instruction rs1 rs2 known, reg_andi_check_v7395 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8448, check_v8449, check_v8450, check_v8451, check_v8452, check_v8453, check_v8454, check_v8455, check_v8456, check_v8457, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_andi
private theorem reg_slli_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 4115 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 4115 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 4115 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 4115 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 4115 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 4115 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 4115 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 4115 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 4115 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 4115 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 4115 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 4115 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 4115 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7355 instruction rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 4115 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7359 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7359 instruction rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 4115 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7363 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7363 instruction rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 4115 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7367 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7367 instruction rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 4115 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7371 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7371 instruction rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 4115 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7375 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7375 instruction rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 4115 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7379 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7379 instruction rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 4115 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7383 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7383 instruction rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 4115 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7387 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7387 instruction rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 4115 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7391 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7391 instruction rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 4115 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7395 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7395 instruction rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 4115 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slli_check_v7398 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) : check_v7398 instruction rs1 rs2 = 1 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 4115 :=
    mask_refines instruction 4261441663 4115 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_slli (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4115) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_slli_check_v7303 instruction rs1 rs2 known, reg_slli_check_v7307 instruction rs1 rs2 known, reg_slli_check_v7311 instruction rs1 rs2 known, reg_slli_check_v7315 instruction rs1 rs2 known, reg_slli_check_v7319 instruction rs1 rs2 known, reg_slli_check_v7323 instruction rs1 rs2 known, reg_slli_check_v7327 instruction rs1 rs2 known, reg_slli_check_v7331 instruction rs1 rs2 known, reg_slli_check_v7335 instruction rs1 rs2 known, reg_slli_check_v7339 instruction rs1 rs2 known, reg_slli_check_v7343 instruction rs1 rs2 known, reg_slli_check_v7347 instruction rs1 rs2 known, reg_slli_check_v7351 instruction rs1 rs2 known, reg_slli_check_v7355 instruction rs1 rs2 known, reg_slli_check_v7359 instruction rs1 rs2 known, reg_slli_check_v7363 instruction rs1 rs2 known, reg_slli_check_v7367 instruction rs1 rs2 known, reg_slli_check_v7371 instruction rs1 rs2 known, reg_slli_check_v7375 instruction rs1 rs2 known, reg_slli_check_v7379 instruction rs1 rs2 known, reg_slli_check_v7383 instruction rs1 rs2 known, reg_slli_check_v7387 instruction rs1 rs2 known, reg_slli_check_v7391 instruction rs1 rs2 known, reg_slli_check_v7395 instruction rs1 rs2 known, reg_slli_check_v7398 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8447, check_v8448, check_v8449, check_v8450, check_v8451, check_v8452, check_v8453, check_v8454, check_v8455, check_v8456, check_v8457, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_slli
private theorem reg_srli_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 20499 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 20499 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 20499 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 20499 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 20499 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 20499 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 20499 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 20499 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 20499 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 20499 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 20499 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 20499 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 20499 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7355 instruction rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 20499 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7359 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7359 instruction rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 20499 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7363 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7363 instruction rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 20499 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7367 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7367 instruction rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 20499 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7371 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7371 instruction rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 20499 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7375 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7375 instruction rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 20499 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7379 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7379 instruction rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 20499 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7383 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7383 instruction rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 20499 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7387 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7387 instruction rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 20499 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7391 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7391 instruction rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 20499 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7395 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7395 instruction rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 20499 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7398 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7398 instruction rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 20499 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srli_check_v7401 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) : check_v7401 instruction rs1 rs2 = 1 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 20499 :=
    mask_refines instruction 4261441663 20499 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_srli (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20499) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_srli_check_v7303 instruction rs1 rs2 known, reg_srli_check_v7307 instruction rs1 rs2 known, reg_srli_check_v7311 instruction rs1 rs2 known, reg_srli_check_v7315 instruction rs1 rs2 known, reg_srli_check_v7319 instruction rs1 rs2 known, reg_srli_check_v7323 instruction rs1 rs2 known, reg_srli_check_v7327 instruction rs1 rs2 known, reg_srli_check_v7331 instruction rs1 rs2 known, reg_srli_check_v7335 instruction rs1 rs2 known, reg_srli_check_v7339 instruction rs1 rs2 known, reg_srli_check_v7343 instruction rs1 rs2 known, reg_srli_check_v7347 instruction rs1 rs2 known, reg_srli_check_v7351 instruction rs1 rs2 known, reg_srli_check_v7355 instruction rs1 rs2 known, reg_srli_check_v7359 instruction rs1 rs2 known, reg_srli_check_v7363 instruction rs1 rs2 known, reg_srli_check_v7367 instruction rs1 rs2 known, reg_srli_check_v7371 instruction rs1 rs2 known, reg_srli_check_v7375 instruction rs1 rs2 known, reg_srli_check_v7379 instruction rs1 rs2 known, reg_srli_check_v7383 instruction rs1 rs2 known, reg_srli_check_v7387 instruction rs1 rs2 known, reg_srli_check_v7391 instruction rs1 rs2 known, reg_srli_check_v7395 instruction rs1 rs2 known, reg_srli_check_v7398 instruction rs1 rs2 known, reg_srli_check_v7401 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8446, check_v8447, check_v8448, check_v8449, check_v8450, check_v8451, check_v8452, check_v8453, check_v8454, check_v8455, check_v8456, check_v8457, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_srli
private theorem reg_srai_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 1073762323 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 1073762323 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 1073762323 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 1073762323 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 1073762323 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 1073762323 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 1073762323 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 1073762323 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 1073762323 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 1073762323 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 1073762323 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 1073762323 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 1073762323 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7355 instruction rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 1073762323 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7359 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7359 instruction rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 1073762323 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7363 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7363 instruction rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 1073762323 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7367 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7367 instruction rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 1073762323 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7371 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7371 instruction rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 1073762323 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7375 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7375 instruction rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 1073762323 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7379 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7379 instruction rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 1073762323 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7383 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7383 instruction rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 1073762323 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7387 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7387 instruction rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 1073762323 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7391 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7391 instruction rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 1073762323 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7395 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7395 instruction rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 1073762323 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7398 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7398 instruction rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 1073762323 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7401 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7401 instruction rs1 rs2 = 0 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20499 :=
    mask_incompatible instruction 4261441663 1073762323 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srai_check_v7404 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) : check_v7404 instruction rs1 rs2 = 1 := by
  change (if (1073762323 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 1073762323 :=
    mask_refines instruction 4261441663 1073762323 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_srai (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762323) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_srai_check_v7303 instruction rs1 rs2 known, reg_srai_check_v7307 instruction rs1 rs2 known, reg_srai_check_v7311 instruction rs1 rs2 known, reg_srai_check_v7315 instruction rs1 rs2 known, reg_srai_check_v7319 instruction rs1 rs2 known, reg_srai_check_v7323 instruction rs1 rs2 known, reg_srai_check_v7327 instruction rs1 rs2 known, reg_srai_check_v7331 instruction rs1 rs2 known, reg_srai_check_v7335 instruction rs1 rs2 known, reg_srai_check_v7339 instruction rs1 rs2 known, reg_srai_check_v7343 instruction rs1 rs2 known, reg_srai_check_v7347 instruction rs1 rs2 known, reg_srai_check_v7351 instruction rs1 rs2 known, reg_srai_check_v7355 instruction rs1 rs2 known, reg_srai_check_v7359 instruction rs1 rs2 known, reg_srai_check_v7363 instruction rs1 rs2 known, reg_srai_check_v7367 instruction rs1 rs2 known, reg_srai_check_v7371 instruction rs1 rs2 known, reg_srai_check_v7375 instruction rs1 rs2 known, reg_srai_check_v7379 instruction rs1 rs2 known, reg_srai_check_v7383 instruction rs1 rs2 known, reg_srai_check_v7387 instruction rs1 rs2 known, reg_srai_check_v7391 instruction rs1 rs2 known, reg_srai_check_v7395 instruction rs1 rs2 known, reg_srai_check_v7398 instruction rs1 rs2 known, reg_srai_check_v7401 instruction rs1 rs2 known, reg_srai_check_v7404 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8445, check_v8446, check_v8447, check_v8448, check_v8449, check_v8450, check_v8451, check_v8452, check_v8453, check_v8454, check_v8455, check_v8456, check_v8457, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_srai
private theorem reg_add_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 51 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 51 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 51 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 51 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 51 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 51 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 51 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 51 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 51 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 51 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 51 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 51 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 51 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7355 instruction rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 51 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7359 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7359 instruction rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 51 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7363 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7363 instruction rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 51 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7367 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7367 instruction rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 51 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7371 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7371 instruction rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 51 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7375 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7375 instruction rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 51 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7379 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7379 instruction rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 51 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7383 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7383 instruction rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 51 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7387 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7387 instruction rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 51 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7391 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7391 instruction rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 51 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7395 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7395 instruction rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 51 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7398 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7398 instruction rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 51 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7401 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7401 instruction rs1 rs2 = 0 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20499 :=
    mask_incompatible instruction 4261441663 51 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7404 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7404 instruction rs1 rs2 = 0 := by
  change (if (1073762323 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762323 :=
    mask_incompatible instruction 4261441663 51 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_add_check_v7407 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) : check_v7407 instruction rs1 rs2 = 1 := by
  change (if (51 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 51 :=
    mask_refines instruction 4261441663 51 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_add (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 51) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_add_check_v7303 instruction rs1 rs2 known, reg_add_check_v7307 instruction rs1 rs2 known, reg_add_check_v7311 instruction rs1 rs2 known, reg_add_check_v7315 instruction rs1 rs2 known, reg_add_check_v7319 instruction rs1 rs2 known, reg_add_check_v7323 instruction rs1 rs2 known, reg_add_check_v7327 instruction rs1 rs2 known, reg_add_check_v7331 instruction rs1 rs2 known, reg_add_check_v7335 instruction rs1 rs2 known, reg_add_check_v7339 instruction rs1 rs2 known, reg_add_check_v7343 instruction rs1 rs2 known, reg_add_check_v7347 instruction rs1 rs2 known, reg_add_check_v7351 instruction rs1 rs2 known, reg_add_check_v7355 instruction rs1 rs2 known, reg_add_check_v7359 instruction rs1 rs2 known, reg_add_check_v7363 instruction rs1 rs2 known, reg_add_check_v7367 instruction rs1 rs2 known, reg_add_check_v7371 instruction rs1 rs2 known, reg_add_check_v7375 instruction rs1 rs2 known, reg_add_check_v7379 instruction rs1 rs2 known, reg_add_check_v7383 instruction rs1 rs2 known, reg_add_check_v7387 instruction rs1 rs2 known, reg_add_check_v7391 instruction rs1 rs2 known, reg_add_check_v7395 instruction rs1 rs2 known, reg_add_check_v7398 instruction rs1 rs2 known, reg_add_check_v7401 instruction rs1 rs2 known, reg_add_check_v7404 instruction rs1 rs2 known, reg_add_check_v7407 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8444, check_v8445, check_v8446, check_v8447, check_v8448, check_v8449, check_v8450, check_v8451, check_v8452, check_v8453, check_v8454, check_v8455, check_v8456, check_v8457, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_add
private theorem reg_sub_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 1073741875 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 1073741875 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 1073741875 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 1073741875 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 1073741875 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 1073741875 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 1073741875 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 1073741875 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 1073741875 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 1073741875 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 1073741875 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 1073741875 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 1073741875 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7355 instruction rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 1073741875 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7359 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7359 instruction rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 1073741875 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7363 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7363 instruction rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 1073741875 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7367 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7367 instruction rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 1073741875 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7371 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7371 instruction rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 1073741875 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7375 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7375 instruction rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 1073741875 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7379 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7379 instruction rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 1073741875 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7383 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7383 instruction rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 1073741875 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7387 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7387 instruction rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 1073741875 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7391 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7391 instruction rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 1073741875 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7395 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7395 instruction rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 1073741875 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7398 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7398 instruction rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 1073741875 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7401 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7401 instruction rs1 rs2 = 0 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20499 :=
    mask_incompatible instruction 4261441663 1073741875 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7404 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7404 instruction rs1 rs2 = 0 := by
  change (if (1073762323 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762323 :=
    mask_incompatible instruction 4261441663 1073741875 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7407 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7407 instruction rs1 rs2 = 0 := by
  change (if (51 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 51 :=
    mask_incompatible instruction 4261441663 1073741875 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sub_check_v7410 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) : check_v7410 instruction rs1 rs2 = 1 := by
  change (if (1073741875 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 1073741875 :=
    mask_refines instruction 4261441663 1073741875 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_sub (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073741875) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_sub_check_v7303 instruction rs1 rs2 known, reg_sub_check_v7307 instruction rs1 rs2 known, reg_sub_check_v7311 instruction rs1 rs2 known, reg_sub_check_v7315 instruction rs1 rs2 known, reg_sub_check_v7319 instruction rs1 rs2 known, reg_sub_check_v7323 instruction rs1 rs2 known, reg_sub_check_v7327 instruction rs1 rs2 known, reg_sub_check_v7331 instruction rs1 rs2 known, reg_sub_check_v7335 instruction rs1 rs2 known, reg_sub_check_v7339 instruction rs1 rs2 known, reg_sub_check_v7343 instruction rs1 rs2 known, reg_sub_check_v7347 instruction rs1 rs2 known, reg_sub_check_v7351 instruction rs1 rs2 known, reg_sub_check_v7355 instruction rs1 rs2 known, reg_sub_check_v7359 instruction rs1 rs2 known, reg_sub_check_v7363 instruction rs1 rs2 known, reg_sub_check_v7367 instruction rs1 rs2 known, reg_sub_check_v7371 instruction rs1 rs2 known, reg_sub_check_v7375 instruction rs1 rs2 known, reg_sub_check_v7379 instruction rs1 rs2 known, reg_sub_check_v7383 instruction rs1 rs2 known, reg_sub_check_v7387 instruction rs1 rs2 known, reg_sub_check_v7391 instruction rs1 rs2 known, reg_sub_check_v7395 instruction rs1 rs2 known, reg_sub_check_v7398 instruction rs1 rs2 known, reg_sub_check_v7401 instruction rs1 rs2 known, reg_sub_check_v7404 instruction rs1 rs2 known, reg_sub_check_v7407 instruction rs1 rs2 known, reg_sub_check_v7410 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8443, check_v8444, check_v8445, check_v8446, check_v8447, check_v8448, check_v8449, check_v8450, check_v8451, check_v8452, check_v8453, check_v8454, check_v8455, check_v8456, check_v8457, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_sub
private theorem reg_sll_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 4147 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 4147 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 4147 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 4147 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 4147 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 4147 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 4147 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 4147 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 4147 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 4147 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 4147 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 4147 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 4147 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7355 instruction rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 4147 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7359 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7359 instruction rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 4147 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7363 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7363 instruction rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 4147 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7367 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7367 instruction rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 4147 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7371 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7371 instruction rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 4147 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7375 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7375 instruction rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 4147 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7379 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7379 instruction rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 4147 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7383 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7383 instruction rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 4147 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7387 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7387 instruction rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 4147 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7391 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7391 instruction rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 4147 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7395 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7395 instruction rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 4147 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7398 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7398 instruction rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 4147 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7401 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7401 instruction rs1 rs2 = 0 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20499 :=
    mask_incompatible instruction 4261441663 4147 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7404 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7404 instruction rs1 rs2 = 0 := by
  change (if (1073762323 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762323 :=
    mask_incompatible instruction 4261441663 4147 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7407 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7407 instruction rs1 rs2 = 0 := by
  change (if (51 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 51 :=
    mask_incompatible instruction 4261441663 4147 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7410 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7410 instruction rs1 rs2 = 0 := by
  change (if (1073741875 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073741875 :=
    mask_incompatible instruction 4261441663 4147 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sll_check_v7413 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) : check_v7413 instruction rs1 rs2 = 1 := by
  change (if (4147 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 4147 :=
    mask_refines instruction 4261441663 4147 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_sll (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 4147) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_sll_check_v7303 instruction rs1 rs2 known, reg_sll_check_v7307 instruction rs1 rs2 known, reg_sll_check_v7311 instruction rs1 rs2 known, reg_sll_check_v7315 instruction rs1 rs2 known, reg_sll_check_v7319 instruction rs1 rs2 known, reg_sll_check_v7323 instruction rs1 rs2 known, reg_sll_check_v7327 instruction rs1 rs2 known, reg_sll_check_v7331 instruction rs1 rs2 known, reg_sll_check_v7335 instruction rs1 rs2 known, reg_sll_check_v7339 instruction rs1 rs2 known, reg_sll_check_v7343 instruction rs1 rs2 known, reg_sll_check_v7347 instruction rs1 rs2 known, reg_sll_check_v7351 instruction rs1 rs2 known, reg_sll_check_v7355 instruction rs1 rs2 known, reg_sll_check_v7359 instruction rs1 rs2 known, reg_sll_check_v7363 instruction rs1 rs2 known, reg_sll_check_v7367 instruction rs1 rs2 known, reg_sll_check_v7371 instruction rs1 rs2 known, reg_sll_check_v7375 instruction rs1 rs2 known, reg_sll_check_v7379 instruction rs1 rs2 known, reg_sll_check_v7383 instruction rs1 rs2 known, reg_sll_check_v7387 instruction rs1 rs2 known, reg_sll_check_v7391 instruction rs1 rs2 known, reg_sll_check_v7395 instruction rs1 rs2 known, reg_sll_check_v7398 instruction rs1 rs2 known, reg_sll_check_v7401 instruction rs1 rs2 known, reg_sll_check_v7404 instruction rs1 rs2 known, reg_sll_check_v7407 instruction rs1 rs2 known, reg_sll_check_v7410 instruction rs1 rs2 known, reg_sll_check_v7413 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8442, check_v8443, check_v8444, check_v8445, check_v8446, check_v8447, check_v8448, check_v8449, check_v8450, check_v8451, check_v8452, check_v8453, check_v8454, check_v8455, check_v8456, check_v8457, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_sll
private theorem reg_slt_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 8243 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 8243 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 8243 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 8243 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 8243 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 8243 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 8243 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 8243 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 8243 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 8243 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 8243 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 8243 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 8243 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7355 instruction rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 8243 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7359 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7359 instruction rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 8243 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7363 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7363 instruction rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 8243 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7367 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7367 instruction rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 8243 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7371 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7371 instruction rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 8243 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7375 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7375 instruction rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 8243 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7379 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7379 instruction rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 8243 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7383 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7383 instruction rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 8243 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7387 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7387 instruction rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 8243 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7391 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7391 instruction rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 8243 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7395 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7395 instruction rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 8243 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7398 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7398 instruction rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 8243 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7401 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7401 instruction rs1 rs2 = 0 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20499 :=
    mask_incompatible instruction 4261441663 8243 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7404 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7404 instruction rs1 rs2 = 0 := by
  change (if (1073762323 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762323 :=
    mask_incompatible instruction 4261441663 8243 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7407 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7407 instruction rs1 rs2 = 0 := by
  change (if (51 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 51 :=
    mask_incompatible instruction 4261441663 8243 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7410 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7410 instruction rs1 rs2 = 0 := by
  change (if (1073741875 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073741875 :=
    mask_incompatible instruction 4261441663 8243 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7413 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7413 instruction rs1 rs2 = 0 := by
  change (if (4147 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4147 :=
    mask_incompatible instruction 4261441663 8243 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_slt_check_v7416 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) : check_v7416 instruction rs1 rs2 = 1 := by
  change (if (8243 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 8243 :=
    mask_refines instruction 4261441663 8243 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_slt (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 8243) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_slt_check_v7303 instruction rs1 rs2 known, reg_slt_check_v7307 instruction rs1 rs2 known, reg_slt_check_v7311 instruction rs1 rs2 known, reg_slt_check_v7315 instruction rs1 rs2 known, reg_slt_check_v7319 instruction rs1 rs2 known, reg_slt_check_v7323 instruction rs1 rs2 known, reg_slt_check_v7327 instruction rs1 rs2 known, reg_slt_check_v7331 instruction rs1 rs2 known, reg_slt_check_v7335 instruction rs1 rs2 known, reg_slt_check_v7339 instruction rs1 rs2 known, reg_slt_check_v7343 instruction rs1 rs2 known, reg_slt_check_v7347 instruction rs1 rs2 known, reg_slt_check_v7351 instruction rs1 rs2 known, reg_slt_check_v7355 instruction rs1 rs2 known, reg_slt_check_v7359 instruction rs1 rs2 known, reg_slt_check_v7363 instruction rs1 rs2 known, reg_slt_check_v7367 instruction rs1 rs2 known, reg_slt_check_v7371 instruction rs1 rs2 known, reg_slt_check_v7375 instruction rs1 rs2 known, reg_slt_check_v7379 instruction rs1 rs2 known, reg_slt_check_v7383 instruction rs1 rs2 known, reg_slt_check_v7387 instruction rs1 rs2 known, reg_slt_check_v7391 instruction rs1 rs2 known, reg_slt_check_v7395 instruction rs1 rs2 known, reg_slt_check_v7398 instruction rs1 rs2 known, reg_slt_check_v7401 instruction rs1 rs2 known, reg_slt_check_v7404 instruction rs1 rs2 known, reg_slt_check_v7407 instruction rs1 rs2 known, reg_slt_check_v7410 instruction rs1 rs2 known, reg_slt_check_v7413 instruction rs1 rs2 known, reg_slt_check_v7416 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8441, check_v8442, check_v8443, check_v8444, check_v8445, check_v8446, check_v8447, check_v8448, check_v8449, check_v8450, check_v8451, check_v8452, check_v8453, check_v8454, check_v8455, check_v8456, check_v8457, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_slt
private theorem reg_sltu_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 12339 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 12339 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 12339 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 12339 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 12339 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 12339 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 12339 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 12339 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 12339 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 12339 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 12339 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 12339 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 12339 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7355 instruction rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 12339 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7359 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7359 instruction rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 12339 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7363 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7363 instruction rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 12339 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7367 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7367 instruction rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 12339 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7371 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7371 instruction rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 12339 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7375 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7375 instruction rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 12339 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7379 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7379 instruction rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 12339 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7383 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7383 instruction rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 12339 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7387 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7387 instruction rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 12339 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7391 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7391 instruction rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 12339 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7395 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7395 instruction rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 12339 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7398 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7398 instruction rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 12339 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7401 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7401 instruction rs1 rs2 = 0 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20499 :=
    mask_incompatible instruction 4261441663 12339 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7404 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7404 instruction rs1 rs2 = 0 := by
  change (if (1073762323 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762323 :=
    mask_incompatible instruction 4261441663 12339 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7407 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7407 instruction rs1 rs2 = 0 := by
  change (if (51 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 51 :=
    mask_incompatible instruction 4261441663 12339 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7410 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7410 instruction rs1 rs2 = 0 := by
  change (if (1073741875 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073741875 :=
    mask_incompatible instruction 4261441663 12339 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7413 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7413 instruction rs1 rs2 = 0 := by
  change (if (4147 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4147 :=
    mask_incompatible instruction 4261441663 12339 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7416 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7416 instruction rs1 rs2 = 0 := by
  change (if (8243 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 8243 :=
    mask_incompatible instruction 4261441663 12339 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sltu_check_v7419 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) : check_v7419 instruction rs1 rs2 = 1 := by
  change (if (12339 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 12339 :=
    mask_refines instruction 4261441663 12339 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_sltu (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 12339) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_sltu_check_v7303 instruction rs1 rs2 known, reg_sltu_check_v7307 instruction rs1 rs2 known, reg_sltu_check_v7311 instruction rs1 rs2 known, reg_sltu_check_v7315 instruction rs1 rs2 known, reg_sltu_check_v7319 instruction rs1 rs2 known, reg_sltu_check_v7323 instruction rs1 rs2 known, reg_sltu_check_v7327 instruction rs1 rs2 known, reg_sltu_check_v7331 instruction rs1 rs2 known, reg_sltu_check_v7335 instruction rs1 rs2 known, reg_sltu_check_v7339 instruction rs1 rs2 known, reg_sltu_check_v7343 instruction rs1 rs2 known, reg_sltu_check_v7347 instruction rs1 rs2 known, reg_sltu_check_v7351 instruction rs1 rs2 known, reg_sltu_check_v7355 instruction rs1 rs2 known, reg_sltu_check_v7359 instruction rs1 rs2 known, reg_sltu_check_v7363 instruction rs1 rs2 known, reg_sltu_check_v7367 instruction rs1 rs2 known, reg_sltu_check_v7371 instruction rs1 rs2 known, reg_sltu_check_v7375 instruction rs1 rs2 known, reg_sltu_check_v7379 instruction rs1 rs2 known, reg_sltu_check_v7383 instruction rs1 rs2 known, reg_sltu_check_v7387 instruction rs1 rs2 known, reg_sltu_check_v7391 instruction rs1 rs2 known, reg_sltu_check_v7395 instruction rs1 rs2 known, reg_sltu_check_v7398 instruction rs1 rs2 known, reg_sltu_check_v7401 instruction rs1 rs2 known, reg_sltu_check_v7404 instruction rs1 rs2 known, reg_sltu_check_v7407 instruction rs1 rs2 known, reg_sltu_check_v7410 instruction rs1 rs2 known, reg_sltu_check_v7413 instruction rs1 rs2 known, reg_sltu_check_v7416 instruction rs1 rs2 known, reg_sltu_check_v7419 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8440, check_v8441, check_v8442, check_v8443, check_v8444, check_v8445, check_v8446, check_v8447, check_v8448, check_v8449, check_v8450, check_v8451, check_v8452, check_v8453, check_v8454, check_v8455, check_v8456, check_v8457, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_sltu
private theorem reg_xor_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 16435 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 16435 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 16435 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 16435 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 16435 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 16435 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 16435 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 16435 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 16435 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 16435 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 16435 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 16435 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 16435 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7355 instruction rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 16435 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7359 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7359 instruction rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 16435 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7363 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7363 instruction rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 16435 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7367 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7367 instruction rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 16435 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7371 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7371 instruction rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 16435 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7375 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7375 instruction rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 16435 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7379 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7379 instruction rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 16435 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7383 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7383 instruction rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 16435 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7387 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7387 instruction rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 16435 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7391 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7391 instruction rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 16435 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7395 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7395 instruction rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 16435 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7398 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7398 instruction rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 16435 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7401 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7401 instruction rs1 rs2 = 0 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20499 :=
    mask_incompatible instruction 4261441663 16435 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7404 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7404 instruction rs1 rs2 = 0 := by
  change (if (1073762323 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762323 :=
    mask_incompatible instruction 4261441663 16435 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7407 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7407 instruction rs1 rs2 = 0 := by
  change (if (51 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 51 :=
    mask_incompatible instruction 4261441663 16435 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7410 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7410 instruction rs1 rs2 = 0 := by
  change (if (1073741875 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073741875 :=
    mask_incompatible instruction 4261441663 16435 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7413 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7413 instruction rs1 rs2 = 0 := by
  change (if (4147 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4147 :=
    mask_incompatible instruction 4261441663 16435 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7416 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7416 instruction rs1 rs2 = 0 := by
  change (if (8243 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 8243 :=
    mask_incompatible instruction 4261441663 16435 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7419 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7419 instruction rs1 rs2 = 0 := by
  change (if (12339 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 12339 :=
    mask_incompatible instruction 4261441663 16435 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_xor_check_v7422 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) : check_v7422 instruction rs1 rs2 = 1 := by
  change (if (16435 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 16435 :=
    mask_refines instruction 4261441663 16435 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_xor (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 16435) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_xor_check_v7303 instruction rs1 rs2 known, reg_xor_check_v7307 instruction rs1 rs2 known, reg_xor_check_v7311 instruction rs1 rs2 known, reg_xor_check_v7315 instruction rs1 rs2 known, reg_xor_check_v7319 instruction rs1 rs2 known, reg_xor_check_v7323 instruction rs1 rs2 known, reg_xor_check_v7327 instruction rs1 rs2 known, reg_xor_check_v7331 instruction rs1 rs2 known, reg_xor_check_v7335 instruction rs1 rs2 known, reg_xor_check_v7339 instruction rs1 rs2 known, reg_xor_check_v7343 instruction rs1 rs2 known, reg_xor_check_v7347 instruction rs1 rs2 known, reg_xor_check_v7351 instruction rs1 rs2 known, reg_xor_check_v7355 instruction rs1 rs2 known, reg_xor_check_v7359 instruction rs1 rs2 known, reg_xor_check_v7363 instruction rs1 rs2 known, reg_xor_check_v7367 instruction rs1 rs2 known, reg_xor_check_v7371 instruction rs1 rs2 known, reg_xor_check_v7375 instruction rs1 rs2 known, reg_xor_check_v7379 instruction rs1 rs2 known, reg_xor_check_v7383 instruction rs1 rs2 known, reg_xor_check_v7387 instruction rs1 rs2 known, reg_xor_check_v7391 instruction rs1 rs2 known, reg_xor_check_v7395 instruction rs1 rs2 known, reg_xor_check_v7398 instruction rs1 rs2 known, reg_xor_check_v7401 instruction rs1 rs2 known, reg_xor_check_v7404 instruction rs1 rs2 known, reg_xor_check_v7407 instruction rs1 rs2 known, reg_xor_check_v7410 instruction rs1 rs2 known, reg_xor_check_v7413 instruction rs1 rs2 known, reg_xor_check_v7416 instruction rs1 rs2 known, reg_xor_check_v7419 instruction rs1 rs2 known, reg_xor_check_v7422 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8439, check_v8440, check_v8441, check_v8442, check_v8443, check_v8444, check_v8445, check_v8446, check_v8447, check_v8448, check_v8449, check_v8450, check_v8451, check_v8452, check_v8453, check_v8454, check_v8455, check_v8456, check_v8457, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_xor
private theorem reg_srl_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 20531 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 20531 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 20531 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 20531 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 20531 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 20531 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 20531 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 20531 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 20531 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 20531 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 20531 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 20531 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 20531 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7355 instruction rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 20531 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7359 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7359 instruction rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 20531 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7363 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7363 instruction rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 20531 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7367 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7367 instruction rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 20531 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7371 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7371 instruction rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 20531 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7375 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7375 instruction rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 20531 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7379 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7379 instruction rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 20531 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7383 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7383 instruction rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 20531 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7387 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7387 instruction rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 20531 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7391 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7391 instruction rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 20531 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7395 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7395 instruction rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 20531 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7398 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7398 instruction rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 20531 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7401 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7401 instruction rs1 rs2 = 0 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20499 :=
    mask_incompatible instruction 4261441663 20531 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7404 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7404 instruction rs1 rs2 = 0 := by
  change (if (1073762323 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762323 :=
    mask_incompatible instruction 4261441663 20531 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7407 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7407 instruction rs1 rs2 = 0 := by
  change (if (51 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 51 :=
    mask_incompatible instruction 4261441663 20531 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7410 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7410 instruction rs1 rs2 = 0 := by
  change (if (1073741875 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073741875 :=
    mask_incompatible instruction 4261441663 20531 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7413 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7413 instruction rs1 rs2 = 0 := by
  change (if (4147 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4147 :=
    mask_incompatible instruction 4261441663 20531 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7416 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7416 instruction rs1 rs2 = 0 := by
  change (if (8243 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 8243 :=
    mask_incompatible instruction 4261441663 20531 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7419 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7419 instruction rs1 rs2 = 0 := by
  change (if (12339 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 12339 :=
    mask_incompatible instruction 4261441663 20531 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7422 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7422 instruction rs1 rs2 = 0 := by
  change (if (16435 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 16435 :=
    mask_incompatible instruction 4261441663 20531 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_srl_check_v7425 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) : check_v7425 instruction rs1 rs2 = 1 := by
  change (if (20531 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 20531 :=
    mask_refines instruction 4261441663 20531 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_srl (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 20531) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_srl_check_v7303 instruction rs1 rs2 known, reg_srl_check_v7307 instruction rs1 rs2 known, reg_srl_check_v7311 instruction rs1 rs2 known, reg_srl_check_v7315 instruction rs1 rs2 known, reg_srl_check_v7319 instruction rs1 rs2 known, reg_srl_check_v7323 instruction rs1 rs2 known, reg_srl_check_v7327 instruction rs1 rs2 known, reg_srl_check_v7331 instruction rs1 rs2 known, reg_srl_check_v7335 instruction rs1 rs2 known, reg_srl_check_v7339 instruction rs1 rs2 known, reg_srl_check_v7343 instruction rs1 rs2 known, reg_srl_check_v7347 instruction rs1 rs2 known, reg_srl_check_v7351 instruction rs1 rs2 known, reg_srl_check_v7355 instruction rs1 rs2 known, reg_srl_check_v7359 instruction rs1 rs2 known, reg_srl_check_v7363 instruction rs1 rs2 known, reg_srl_check_v7367 instruction rs1 rs2 known, reg_srl_check_v7371 instruction rs1 rs2 known, reg_srl_check_v7375 instruction rs1 rs2 known, reg_srl_check_v7379 instruction rs1 rs2 known, reg_srl_check_v7383 instruction rs1 rs2 known, reg_srl_check_v7387 instruction rs1 rs2 known, reg_srl_check_v7391 instruction rs1 rs2 known, reg_srl_check_v7395 instruction rs1 rs2 known, reg_srl_check_v7398 instruction rs1 rs2 known, reg_srl_check_v7401 instruction rs1 rs2 known, reg_srl_check_v7404 instruction rs1 rs2 known, reg_srl_check_v7407 instruction rs1 rs2 known, reg_srl_check_v7410 instruction rs1 rs2 known, reg_srl_check_v7413 instruction rs1 rs2 known, reg_srl_check_v7416 instruction rs1 rs2 known, reg_srl_check_v7419 instruction rs1 rs2 known, reg_srl_check_v7422 instruction rs1 rs2 known, reg_srl_check_v7425 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8438, check_v8439, check_v8440, check_v8441, check_v8442, check_v8443, check_v8444, check_v8445, check_v8446, check_v8447, check_v8448, check_v8449, check_v8450, check_v8451, check_v8452, check_v8453, check_v8454, check_v8455, check_v8456, check_v8457, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_srl
private theorem reg_sra_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 1073762355 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 1073762355 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 1073762355 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 1073762355 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 1073762355 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 1073762355 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 1073762355 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 1073762355 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 1073762355 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 1073762355 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 1073762355 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 1073762355 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 1073762355 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7355 instruction rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 1073762355 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7359 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7359 instruction rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 1073762355 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7363 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7363 instruction rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 1073762355 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7367 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7367 instruction rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 1073762355 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7371 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7371 instruction rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 1073762355 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7375 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7375 instruction rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 1073762355 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7379 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7379 instruction rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 1073762355 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7383 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7383 instruction rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 1073762355 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7387 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7387 instruction rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 1073762355 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7391 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7391 instruction rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 1073762355 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7395 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7395 instruction rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 1073762355 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7398 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7398 instruction rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 1073762355 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7401 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7401 instruction rs1 rs2 = 0 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20499 :=
    mask_incompatible instruction 4261441663 1073762355 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7404 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7404 instruction rs1 rs2 = 0 := by
  change (if (1073762323 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762323 :=
    mask_incompatible instruction 4261441663 1073762355 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7407 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7407 instruction rs1 rs2 = 0 := by
  change (if (51 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 51 :=
    mask_incompatible instruction 4261441663 1073762355 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7410 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7410 instruction rs1 rs2 = 0 := by
  change (if (1073741875 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073741875 :=
    mask_incompatible instruction 4261441663 1073762355 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7413 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7413 instruction rs1 rs2 = 0 := by
  change (if (4147 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4147 :=
    mask_incompatible instruction 4261441663 1073762355 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7416 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7416 instruction rs1 rs2 = 0 := by
  change (if (8243 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 8243 :=
    mask_incompatible instruction 4261441663 1073762355 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7419 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7419 instruction rs1 rs2 = 0 := by
  change (if (12339 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 12339 :=
    mask_incompatible instruction 4261441663 1073762355 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7422 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7422 instruction rs1 rs2 = 0 := by
  change (if (16435 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 16435 :=
    mask_incompatible instruction 4261441663 1073762355 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7425 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7425 instruction rs1 rs2 = 0 := by
  change (if (20531 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20531 :=
    mask_incompatible instruction 4261441663 1073762355 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_sra_check_v7428 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) : check_v7428 instruction rs1 rs2 = 1 := by
  change (if (1073762355 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 1073762355 :=
    mask_refines instruction 4261441663 1073762355 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_sra (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 1073762355) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_sra_check_v7303 instruction rs1 rs2 known, reg_sra_check_v7307 instruction rs1 rs2 known, reg_sra_check_v7311 instruction rs1 rs2 known, reg_sra_check_v7315 instruction rs1 rs2 known, reg_sra_check_v7319 instruction rs1 rs2 known, reg_sra_check_v7323 instruction rs1 rs2 known, reg_sra_check_v7327 instruction rs1 rs2 known, reg_sra_check_v7331 instruction rs1 rs2 known, reg_sra_check_v7335 instruction rs1 rs2 known, reg_sra_check_v7339 instruction rs1 rs2 known, reg_sra_check_v7343 instruction rs1 rs2 known, reg_sra_check_v7347 instruction rs1 rs2 known, reg_sra_check_v7351 instruction rs1 rs2 known, reg_sra_check_v7355 instruction rs1 rs2 known, reg_sra_check_v7359 instruction rs1 rs2 known, reg_sra_check_v7363 instruction rs1 rs2 known, reg_sra_check_v7367 instruction rs1 rs2 known, reg_sra_check_v7371 instruction rs1 rs2 known, reg_sra_check_v7375 instruction rs1 rs2 known, reg_sra_check_v7379 instruction rs1 rs2 known, reg_sra_check_v7383 instruction rs1 rs2 known, reg_sra_check_v7387 instruction rs1 rs2 known, reg_sra_check_v7391 instruction rs1 rs2 known, reg_sra_check_v7395 instruction rs1 rs2 known, reg_sra_check_v7398 instruction rs1 rs2 known, reg_sra_check_v7401 instruction rs1 rs2 known, reg_sra_check_v7404 instruction rs1 rs2 known, reg_sra_check_v7407 instruction rs1 rs2 known, reg_sra_check_v7410 instruction rs1 rs2 known, reg_sra_check_v7413 instruction rs1 rs2 known, reg_sra_check_v7416 instruction rs1 rs2 known, reg_sra_check_v7419 instruction rs1 rs2 known, reg_sra_check_v7422 instruction rs1 rs2 known, reg_sra_check_v7425 instruction rs1 rs2 known, reg_sra_check_v7428 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8437, check_v8438, check_v8439, check_v8440, check_v8441, check_v8442, check_v8443, check_v8444, check_v8445, check_v8446, check_v8447, check_v8448, check_v8449, check_v8450, check_v8451, check_v8452, check_v8453, check_v8454, check_v8455, check_v8456, check_v8457, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_sra
private theorem reg_or_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 24627 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 24627 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 24627 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 24627 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 24627 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 24627 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 24627 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 24627 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 24627 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 24627 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 24627 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 24627 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 24627 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7355 instruction rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 24627 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7359 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7359 instruction rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 24627 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7363 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7363 instruction rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 24627 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7367 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7367 instruction rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 24627 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7371 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7371 instruction rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 24627 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7375 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7375 instruction rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 24627 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7379 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7379 instruction rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 24627 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7383 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7383 instruction rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 24627 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7387 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7387 instruction rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 24627 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7391 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7391 instruction rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 24627 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7395 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7395 instruction rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 24627 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7398 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7398 instruction rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 24627 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7401 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7401 instruction rs1 rs2 = 0 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20499 :=
    mask_incompatible instruction 4261441663 24627 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7404 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7404 instruction rs1 rs2 = 0 := by
  change (if (1073762323 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762323 :=
    mask_incompatible instruction 4261441663 24627 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7407 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7407 instruction rs1 rs2 = 0 := by
  change (if (51 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 51 :=
    mask_incompatible instruction 4261441663 24627 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7410 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7410 instruction rs1 rs2 = 0 := by
  change (if (1073741875 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073741875 :=
    mask_incompatible instruction 4261441663 24627 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7413 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7413 instruction rs1 rs2 = 0 := by
  change (if (4147 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4147 :=
    mask_incompatible instruction 4261441663 24627 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7416 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7416 instruction rs1 rs2 = 0 := by
  change (if (8243 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 8243 :=
    mask_incompatible instruction 4261441663 24627 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7419 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7419 instruction rs1 rs2 = 0 := by
  change (if (12339 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 12339 :=
    mask_incompatible instruction 4261441663 24627 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7422 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7422 instruction rs1 rs2 = 0 := by
  change (if (16435 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 16435 :=
    mask_incompatible instruction 4261441663 24627 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7425 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7425 instruction rs1 rs2 = 0 := by
  change (if (20531 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20531 :=
    mask_incompatible instruction 4261441663 24627 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7428 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7428 instruction rs1 rs2 = 0 := by
  change (if (1073762355 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762355 :=
    mask_incompatible instruction 4261441663 24627 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_or_check_v7431 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) : check_v7431 instruction rs1 rs2 = 1 := by
  change (if (24627 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 24627 :=
    mask_refines instruction 4261441663 24627 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_or (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 24627) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_or_check_v7303 instruction rs1 rs2 known, reg_or_check_v7307 instruction rs1 rs2 known, reg_or_check_v7311 instruction rs1 rs2 known, reg_or_check_v7315 instruction rs1 rs2 known, reg_or_check_v7319 instruction rs1 rs2 known, reg_or_check_v7323 instruction rs1 rs2 known, reg_or_check_v7327 instruction rs1 rs2 known, reg_or_check_v7331 instruction rs1 rs2 known, reg_or_check_v7335 instruction rs1 rs2 known, reg_or_check_v7339 instruction rs1 rs2 known, reg_or_check_v7343 instruction rs1 rs2 known, reg_or_check_v7347 instruction rs1 rs2 known, reg_or_check_v7351 instruction rs1 rs2 known, reg_or_check_v7355 instruction rs1 rs2 known, reg_or_check_v7359 instruction rs1 rs2 known, reg_or_check_v7363 instruction rs1 rs2 known, reg_or_check_v7367 instruction rs1 rs2 known, reg_or_check_v7371 instruction rs1 rs2 known, reg_or_check_v7375 instruction rs1 rs2 known, reg_or_check_v7379 instruction rs1 rs2 known, reg_or_check_v7383 instruction rs1 rs2 known, reg_or_check_v7387 instruction rs1 rs2 known, reg_or_check_v7391 instruction rs1 rs2 known, reg_or_check_v7395 instruction rs1 rs2 known, reg_or_check_v7398 instruction rs1 rs2 known, reg_or_check_v7401 instruction rs1 rs2 known, reg_or_check_v7404 instruction rs1 rs2 known, reg_or_check_v7407 instruction rs1 rs2 known, reg_or_check_v7410 instruction rs1 rs2 known, reg_or_check_v7413 instruction rs1 rs2 known, reg_or_check_v7416 instruction rs1 rs2 known, reg_or_check_v7419 instruction rs1 rs2 known, reg_or_check_v7422 instruction rs1 rs2 known, reg_or_check_v7425 instruction rs1 rs2 known, reg_or_check_v7428 instruction rs1 rs2 known, reg_or_check_v7431 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8436, check_v8437, check_v8438, check_v8439, check_v8440, check_v8441, check_v8442, check_v8443, check_v8444, check_v8445, check_v8446, check_v8447, check_v8448, check_v8449, check_v8450, check_v8451, check_v8452, check_v8453, check_v8454, check_v8455, check_v8456, check_v8457, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_or
private theorem reg_and_check_v7303 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7303 instruction rs1 rs2 = 0 := by
  change (if (55 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 55 :=
    mask_incompatible instruction 4261441663 28723 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7307 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7307 instruction rs1 rs2 = 0 := by
  change (if (23 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 23 :=
    mask_incompatible instruction 4261441663 28723 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7311 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7311 instruction rs1 rs2 = 0 := by
  change (if (111 : BitVec 32) = (instruction &&& 127) then 1 else 0) = 0
  have no : instruction &&& 127 ≠ 111 :=
    mask_incompatible instruction 4261441663 28723 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7315 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7315 instruction rs1 rs2 = 0 := by
  change (if (103 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 103 :=
    mask_incompatible instruction 4261441663 28723 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7319 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7319 instruction rs1 rs2 = 0 := by
  change (if (99 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 99 :=
    mask_incompatible instruction 4261441663 28723 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7323 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7323 instruction rs1 rs2 = 0 := by
  change (if (4195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4195 :=
    mask_incompatible instruction 4261441663 28723 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7327 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7327 instruction rs1 rs2 = 0 := by
  change (if (16483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16483 :=
    mask_incompatible instruction 4261441663 28723 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7331 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7331 instruction rs1 rs2 = 0 := by
  change (if (20579 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20579 :=
    mask_incompatible instruction 4261441663 28723 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7335 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7335 instruction rs1 rs2 = 0 := by
  change (if (24675 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24675 :=
    mask_incompatible instruction 4261441663 28723 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7339 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7339 instruction rs1 rs2 = 0 := by
  change (if (28771 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28771 :=
    mask_incompatible instruction 4261441663 28723 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7343 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7343 instruction rs1 rs2 = 0 := by
  change (if (3 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 3 :=
    mask_incompatible instruction 4261441663 28723 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7347 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7347 instruction rs1 rs2 = 0 := by
  change (if (4099 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4099 :=
    mask_incompatible instruction 4261441663 28723 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7351 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7351 instruction rs1 rs2 = 0 := by
  change (if (8195 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8195 :=
    mask_incompatible instruction 4261441663 28723 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7355 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7355 instruction rs1 rs2 = 0 := by
  change (if (16387 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16387 :=
    mask_incompatible instruction 4261441663 28723 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7359 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7359 instruction rs1 rs2 = 0 := by
  change (if (20483 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 20483 :=
    mask_incompatible instruction 4261441663 28723 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7363 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7363 instruction rs1 rs2 = 0 := by
  change (if (35 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 35 :=
    mask_incompatible instruction 4261441663 28723 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7367 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7367 instruction rs1 rs2 = 0 := by
  change (if (4131 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 4131 :=
    mask_incompatible instruction 4261441663 28723 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7371 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7371 instruction rs1 rs2 = 0 := by
  change (if (8227 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8227 :=
    mask_incompatible instruction 4261441663 28723 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7375 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7375 instruction rs1 rs2 = 0 := by
  change (if (19 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 19 :=
    mask_incompatible instruction 4261441663 28723 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7379 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7379 instruction rs1 rs2 = 0 := by
  change (if (8211 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 8211 :=
    mask_incompatible instruction 4261441663 28723 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7383 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7383 instruction rs1 rs2 = 0 := by
  change (if (12307 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 12307 :=
    mask_incompatible instruction 4261441663 28723 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7387 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7387 instruction rs1 rs2 = 0 := by
  change (if (16403 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 16403 :=
    mask_incompatible instruction 4261441663 28723 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7391 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7391 instruction rs1 rs2 = 0 := by
  change (if (24595 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 24595 :=
    mask_incompatible instruction 4261441663 28723 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7395 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7395 instruction rs1 rs2 = 0 := by
  change (if (28691 : BitVec 32) = (instruction &&& 28799) then 1 else 0) = 0
  have no : instruction &&& 28799 ≠ 28691 :=
    mask_incompatible instruction 4261441663 28723 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7398 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7398 instruction rs1 rs2 = 0 := by
  change (if (4115 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4115 :=
    mask_incompatible instruction 4261441663 28723 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7401 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7401 instruction rs1 rs2 = 0 := by
  change (if (20499 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20499 :=
    mask_incompatible instruction 4261441663 28723 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7404 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7404 instruction rs1 rs2 = 0 := by
  change (if (1073762323 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762323 :=
    mask_incompatible instruction 4261441663 28723 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7407 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7407 instruction rs1 rs2 = 0 := by
  change (if (51 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 51 :=
    mask_incompatible instruction 4261441663 28723 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7410 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7410 instruction rs1 rs2 = 0 := by
  change (if (1073741875 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073741875 :=
    mask_incompatible instruction 4261441663 28723 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7413 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7413 instruction rs1 rs2 = 0 := by
  change (if (4147 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 4147 :=
    mask_incompatible instruction 4261441663 28723 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7416 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7416 instruction rs1 rs2 = 0 := by
  change (if (8243 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 8243 :=
    mask_incompatible instruction 4261441663 28723 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7419 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7419 instruction rs1 rs2 = 0 := by
  change (if (12339 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 12339 :=
    mask_incompatible instruction 4261441663 28723 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7422 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7422 instruction rs1 rs2 = 0 := by
  change (if (16435 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 16435 :=
    mask_incompatible instruction 4261441663 28723 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7425 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7425 instruction rs1 rs2 = 0 := by
  change (if (20531 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 20531 :=
    mask_incompatible instruction 4261441663 28723 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7428 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7428 instruction rs1 rs2 = 0 := by
  change (if (1073762355 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 1073762355 :=
    mask_incompatible instruction 4261441663 28723 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7431 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7431 instruction rs1 rs2 = 0 := by
  change (if (24627 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 0
  have no : instruction &&& 4261441663 ≠ 24627 :=
    mask_incompatible instruction 4261441663 28723 4261441663 24627 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reg_and_check_v7434 (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) : check_v7434 instruction rs1 rs2 = 1 := by
  change (if (28723 : BitVec 32) = (instruction &&& 4261441663) then 1 else 0) = 1
  have yes : instruction &&& 4261441663 = 28723 :=
    mask_refines instruction 4261441663 28723 4261441663 known (by decide)
  rw [if_pos yes.symm]
theorem decoded_check_and (instruction rs1 rs2 : BitVec 32)
    (known : instruction &&& 4261441663 = 28723) :
    decodedPcCheck instruction rs1 rs2 = (0) := by
  simp only [decodedPcCheck, check_v200, check_v22, check_v26, check_v261, check_v29, check_v32, check_v4, check_v42, check_v716, reg_and_check_v7303 instruction rs1 rs2 known, reg_and_check_v7307 instruction rs1 rs2 known, reg_and_check_v7311 instruction rs1 rs2 known, reg_and_check_v7315 instruction rs1 rs2 known, reg_and_check_v7319 instruction rs1 rs2 known, reg_and_check_v7323 instruction rs1 rs2 known, reg_and_check_v7327 instruction rs1 rs2 known, reg_and_check_v7331 instruction rs1 rs2 known, reg_and_check_v7335 instruction rs1 rs2 known, reg_and_check_v7339 instruction rs1 rs2 known, reg_and_check_v7343 instruction rs1 rs2 known, reg_and_check_v7347 instruction rs1 rs2 known, reg_and_check_v7351 instruction rs1 rs2 known, reg_and_check_v7355 instruction rs1 rs2 known, reg_and_check_v7359 instruction rs1 rs2 known, reg_and_check_v7363 instruction rs1 rs2 known, reg_and_check_v7367 instruction rs1 rs2 known, reg_and_check_v7371 instruction rs1 rs2 known, reg_and_check_v7375 instruction rs1 rs2 known, reg_and_check_v7379 instruction rs1 rs2 known, reg_and_check_v7383 instruction rs1 rs2 known, reg_and_check_v7387 instruction rs1 rs2 known, reg_and_check_v7391 instruction rs1 rs2 known, reg_and_check_v7395 instruction rs1 rs2 known, reg_and_check_v7398 instruction rs1 rs2 known, reg_and_check_v7401 instruction rs1 rs2 known, reg_and_check_v7404 instruction rs1 rs2 known, reg_and_check_v7407 instruction rs1 rs2 known, reg_and_check_v7410 instruction rs1 rs2 known, reg_and_check_v7413 instruction rs1 rs2 known, reg_and_check_v7416 instruction rs1 rs2 known, reg_and_check_v7419 instruction rs1 rs2 known, reg_and_check_v7422 instruction rs1 rs2 known, reg_and_check_v7425 instruction rs1 rs2 known, reg_and_check_v7428 instruction rs1 rs2 known, reg_and_check_v7431 instruction rs1 rs2 known, reg_and_check_v7434 instruction rs1 rs2 known, check_v7521, check_v7522, check_v7523, check_v7524, check_v7525, check_v7526, check_v7527, check_v7528, check_v7529, check_v7530, check_v7531, check_v7532, check_v7533, check_v7534, check_v7535, check_v7731, check_v7732, check_v7733, check_v7734, check_v7735, check_v7736, check_v7743, check_v7744, check_v7745, check_v7746, check_v7747, check_v7748, check_v7749, check_v7753, check_v7754, check_v7755, check_v7756, check_v7757, check_v7758, check_v7759, check_v8435, check_v8436, check_v8437, check_v8438, check_v8439, check_v8440, check_v8441, check_v8442, check_v8443, check_v8444, check_v8445, check_v8446, check_v8447, check_v8448, check_v8449, check_v8450, check_v8451, check_v8452, check_v8453, check_v8454, check_v8455, check_v8456, check_v8457, check_v8458, check_v8459, check_v8460, check_v8461, check_v8462, check_v8463, check_v8464, check_v8465, check_v8466, check_v8467, check_v8468, check_v8469, check_v8470, check_v8471, check_v8472, check_v8473, check_v8474, check_v8475, BitVec.reduceEq, ↓reduceIte]
  simp
#print axioms decoded_check_and
end RiscvMiniProofs
