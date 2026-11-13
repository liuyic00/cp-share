import Proofs.MulDivSignedMultiplyValue

namespace HierarchicalMulDiv

/-- The signed final digit subtracts two copies of the multiplicand before
    shifting; in the 128-bit product this is one copy shifted by 64 bits. -/
theorem multiply_sign_correction (bits : BitVec 130) (d : BitVec 65)
    (count : BitVec 7) (negative : BitVec 1) :
    (unpackMultiply (multiplyAdvance bits d count negative)).setWidth 128 =
      (unsignedMultiplyAdvance (unpackMultiply bits) d).setWidth 128 -
      (if BitVec.extractLsb' 64 1 bits = 1#1 then d.signExtend 128 <<< 64 else 0#128) := by
  rw [unpack_multiply_advance]
  unfold multiplyAccumulator unsignedMultiplyAdvance unpackMultiply
  by_cases sign : BitVec.extractLsb' 64 1 bits = 1#1
  · simp only [sign, if_pos]
    by_cases low : BitVec.extractLsb' 0 1 bits = 1#1
    · simp only [low, if_pos]
      bv_decide (config := { acNf := true })
    · have zero : BitVec.extractLsb' 0 1 bits = 0#1 := by bv_decide
      simp only [zero]
      rw [show (BitVec.replicate 65 1#1 ++ 0#1) = -(2#66) by bv_decide,
        BitVec.neg_mul, BitVec.two_mul]
      bv_decide (config := { acNf := true })
  · have zero : BitVec.extractLsb' 64 1 bits = 0#1 := by bv_decide
    simp only [zero]
    by_cases low : BitVec.extractLsb' 0 1 bits = 1#1
    · simp only [low]
      bv_decide (config := { acNf := true })
    · have zeroLow : BitVec.extractLsb' 0 1 bits = 0#1 := by bv_decide
      simp only [zeroLow]
      bv_decide (config := { acNf := true })

/-- All 64 packed iterations reduce to the common signed-multiplicand
    recurrence followed by the one final multiplier-sign correction. -/
theorem multiply_complete_correction (bits : BitVec 130) (d : BitVec 65)
    (negative : BitVec 1) (initial : BitVec.extractLsb' 64 1 bits = 0#1) :
    (unpackMultiply (multiplyMany d negative 0 64 bits)).setWidth 128 =
      (unsignedMultiplyMany d 64 (unpackMultiply bits)).setWidth 128 -
      (if negative = 1#1 then d.signExtend 128 <<< 64 else 0#128) := by
  change (unpackMultiply (multiplyAdvance (multiplyMany d negative 0 63 bits) d _ negative)).setWidth 128 = _
  rw [multiply_sign_correction, multiply_final_sign,
    signed_multiply_prefix bits d negative 63 (by omega) initial]
  rfl

#print axioms multiply_complete_correction
#print axioms multiply_sign_correction
end HierarchicalMulDiv
