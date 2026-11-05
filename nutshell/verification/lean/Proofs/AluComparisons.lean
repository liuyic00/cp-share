import Proofs.ArithmeticCompare
namespace NutShellProofs
open nNutCore

theorem alu_sub_intermediate (s : State) (i : Inputs)
    (subtract : BitVec.extractLsb' 6 1 (v28 s i) = 0) :
    v12169 s i = widenedSub (v12148 s i) (v12150 s i) := by
  simp only [v12169, v12168, v12165, v12164, v12157, v12163, v12162,
    v12161, v12159, v12158, v12141, subtract, v24, v12160, v12167, v12166]
  simp only [show (BitVec.ofNat 1 0 : BitVec 1) = 0 by rfl, ↓reduceIte]
  rw [low_add _ _ (by decide), BitVec.extractLsb'_append_eq_of_add_le (by decide)]
  simp only [BitVec.extractLsb'_eq_self]
  change ((0 : BitVec 1) ++ v12148 s i) +
    ((0 : BitVec 1) ++ (v12150 s i ^^^ BitVec.allOnes 64)) + 1 = _
  rw [BitVec.xor_allOnes]
  rfl

theorem alu_unsigned_compare_bit (s : State) (i : Inputs)
    (subtract : BitVec.extractLsb' 6 1 (v28 s i) = 0) :
    v12171 s i = if (v12148 s i).toNat < (v12150 s i).toNat then 1 else 0 := by
  rw [v12171, v12170, alu_sub_intermediate s i subtract, widened_sub_carry]
  split <;> simp [v24]

theorem alu_signed_compare_bit (s : State) (i : Inputs)
    (subtract : BitVec.extractLsb' 6 1 (v28 s i) = 0) :
    v12172 s i = if (v12148 s i).toInt < (v12150 s i).toInt then 1 else 0 := by
  rw [v12172, v12156, v12151, alu_unsigned_compare_bit s i subtract]
  exact signed_compare_from_unsigned _ _

#print axioms alu_signed_compare_bit
#print axioms alu_unsigned_compare_bit
end NutShellProofs
