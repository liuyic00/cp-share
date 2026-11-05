import Proofs.BranchCheckDecode
namespace RiscvMiniProofs
set_option linter.unusedSimpArgs false

theorem branch_sub (instruction a b : BitVec 32) :
    check_v7729 instruction a b = a - b := by
  apply BitVec.eq_of_toNat_eq
  have ha := a.isLt
  have hb := b.isLt
  change (BitVec.extractLsb' 0 32 ((0#1 ++ a) - (0#1 ++ b))).toNat = (a-b).toNat
  have za : (0#1 ++ a).toNat = a.toNat := by simp only [BitVec.toNat_append]; simp
  have zb : (0#1 ++ b).toNat = b.toNat := by simp only [BitVec.toNat_append]; simp
  simp only [BitVec.extractLsb'_toNat, BitVec.toNat_sub, za, zb,
    Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.div_one]
  omega

theorem branch_nonzero (instruction a b : BitVec 32) :
    check_v7730 instruction a b = (if a ≠ b then 1 else 0) := by
  simp [check_v7730, branch_sub, check_v3, BitVec.sub_eq_iff_eq_add]

theorem branch_signed_less (instruction a b : BitVec 32) :
    check_v7742 instruction a b = (if a.toInt < b.toInt then 1 else 0) := by
  simp only [check_v7742, check_v7739, check_v7737, check_v7738, check_v7630, check_v7726, check_v7740, check_v7741, branch_sub]
  have ha := a.isLt
  have hb := b.isLt
  simp only [BitVec.toNat_eq, BitVec.extractLsb'_toNat, BitVec.toNat_sub,
    BitVec.toInt_eq_toNat_cond, apply_ite, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.reducePow]
  have one : (1#1).toNat = 1 := rfl
  have zero : (0#1).toNat = 0 := rfl
  repeat' split
  all_goals simp_all only [BitVec.toNat_eq, BitVec.toNat_ofNat, BitVec.toNat_one (by decide : 0 < 1), BitVec.toNat_zero, Nat.reduceMod]
  all_goals dsimp at *
  all_goals omega
#print axioms branch_signed_less

theorem branch_unsigned_less (instruction a b : BitVec 32) :
    check_v7752 instruction a b = (if a.toNat < b.toNat then 1 else 0) := by
  simp only [check_v7752, check_v7739, check_v7737, check_v7738, check_v7630, check_v7726, check_v7750, check_v7751, branch_sub]
  have ha := a.isLt
  have hb := b.isLt
  simp only [BitVec.toNat_eq, BitVec.extractLsb'_toNat, BitVec.toNat_sub,
    BitVec.toInt_eq_toNat_cond, apply_ite, BitVec.toNat_ofNat,
    Nat.shiftRight_eq_div_pow, Nat.reducePow]
  have one : (1#1).toNat = 1 := rfl
  have zero : (0#1).toNat = 0 := rfl
  repeat' split
  all_goals simp_all only [BitVec.toNat_eq, BitVec.toNat_ofNat, BitVec.toNat_one (by decide : 0 < 1), BitVec.toNat_zero, Nat.reduceMod]
  all_goals dsimp at *
  all_goals omega
#print axioms branch_unsigned_less

#print axioms branch_sub
#print axioms branch_nonzero
theorem decoded_check_beq_semantics (instruction a b : BitVec 32)
    (known : instruction &&& 28799 = 99) :
    decodedPcCheck instruction a b = (if a = b then 1 else 0) := by
  rw [decoded_check_beq _ _ _ known, branch_nonzero]
  by_cases h : a = b <;> simp [h] <;> omega
#print axioms decoded_check_beq_semantics

theorem decoded_check_bne_semantics (instruction a b : BitVec 32)
    (known : instruction &&& 28799 = 4195) :
    decodedPcCheck instruction a b = (if a ≠ b then 1 else 0) := by
  rw [decoded_check_bne _ _ _ known, branch_nonzero]
#print axioms decoded_check_bne_semantics

theorem decoded_check_blt_semantics (instruction a b : BitVec 32)
    (known : instruction &&& 28799 = 16483) :
    decodedPcCheck instruction a b = (if a.toInt < b.toInt then 1 else 0) := by
  rw [decoded_check_blt _ _ _ known, branch_signed_less]
#print axioms decoded_check_blt_semantics

theorem decoded_check_bge_semantics (instruction a b : BitVec 32)
    (known : instruction &&& 28799 = 20579) :
    decodedPcCheck instruction a b = (if b.toInt ≤ a.toInt then 1 else 0) := by
  rw [decoded_check_bge _ _ _ known, branch_signed_less]
  by_cases h : b.toInt ≤ a.toInt <;> simp [h] <;> omega
#print axioms decoded_check_bge_semantics

theorem decoded_check_bltu_semantics (instruction a b : BitVec 32)
    (known : instruction &&& 28799 = 24675) :
    decodedPcCheck instruction a b = (if a.toNat < b.toNat then 1 else 0) := by
  rw [decoded_check_bltu _ _ _ known, branch_unsigned_less]
#print axioms decoded_check_bltu_semantics

theorem decoded_check_bgeu_semantics (instruction a b : BitVec 32)
    (known : instruction &&& 28799 = 28771) :
    decodedPcCheck instruction a b = (if b.toNat ≤ a.toNat then 1 else 0) := by
  rw [decoded_check_bgeu _ _ _ known, branch_unsigned_less]
  by_cases h : b.toNat ≤ a.toNat <;> simp [h] <;> omega
#print axioms decoded_check_bgeu_semantics

end RiscvMiniProofs
