import Proofs.MulDivMultiplyCorrection

namespace HierarchicalMulDiv

/-- The common 64-digit recurrence multiplies an unsigned multiplier by an
    arbitrary signed 65-bit multiplicand exactly. -/
theorem common_signed_product (a : BitVec 64) (d : BitVec 65) :
    (unsignedMultiplyMany d 64 (0#65 ++ a)).toInt = (a.toNat : Int) * d.toInt := by
  rw [signed_iterations_value]
  have initial : (0#65 ++ a).toInt = (a.toNat : Int) := by
    rw [BitVec.toInt_append]
    simp
  rw [initial, HierarchicalSignedMultiply.shiftAddMany_value 63 64 _ _ (by omega),
    HierarchicalSignedMultiply.digitProduct_value]
  have quotient : (a.toNat : Int) / 2 ^ 64 = 0 := by
    have width := a.isLt
    omega
  change (a.toNat : Int) / 18446744073709551616 = 0 at quotient
  simp [quotient]

theorem narrow_signed_product (x : BitVec 129) :
    x.setWidth 128 = BitVec.ofInt 128 x.toInt := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toInt_eq_toNat_cond]
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
  split <;> omega

/-- The common recurrence's low 128 bits are the mathematical signed product
    reduced to the product width. -/
theorem common_signed_product_bits (a : BitVec 64) (d : BitVec 65) :
    (unsignedMultiplyMany d 64 (0#65 ++ a)).setWidth 128 =
      BitVec.ofInt 128 ((a.toNat : Int) * d.toInt) := by
  rw [narrow_signed_product, common_signed_product]

theorem shifted_signed_operand (d : BitVec 65) :
    d.signExtend 128 <<< 64 = BitVec.ofInt 128 (d.toInt * 2 ^ 64) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow, BitVec.ofInt_mul]
  rfl

/-- Complete packed multiplication, with the multiplier interpreted according
    to its captured sign bit and the multiplicand interpreted as signed. -/
theorem signed_packed_product (a : BitVec 64) (d : BitVec 65) (negative : BitVec 1) :
    (unpackMultiply (multiplyMany d negative 0 64 (0#66 ++ a))).setWidth 128 =
      BitVec.ofInt 128 (((a.toNat : Int) - (if negative = 1#1 then 2 ^ 64 else 0)) * d.toInt) := by
  have initial : BitVec.extractLsb' 64 1 (0#66 ++ a) = 0#1 := by bv_decide
  rw [multiply_complete_correction _ _ _ initial, unpack_initial, common_signed_product_bits]
  by_cases sign : negative = 1#1
  · simp only [sign, if_pos, shifted_signed_operand]
    simp [Int.sub_mul, Int.add_mul, Int.neg_mul, Int.sub_eq_add_neg, BitVec.ofInt_add, BitVec.ofInt_neg,
      BitVec.sub_eq_add_neg, Int.mul_comm]
  · simp [sign]

#print axioms signed_packed_product
#print axioms common_signed_product_bits
#print axioms common_signed_product
end HierarchicalMulDiv
