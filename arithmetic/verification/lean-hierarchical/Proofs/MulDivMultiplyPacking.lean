import Proofs.MulDivMultiplyRequest

namespace HierarchicalMulDiv

def unpackMultiply (bits : BitVec 130) : BitVec 129 :=
  BitVec.extractLsb' 65 65 bits ++ BitVec.extractLsb' 0 64 bits

def multiplyAccumulator (bits : BitVec 130) (d : BitVec 65) : BitVec 66 :=
  let digit := BitVec.replicate 65 (BitVec.extractLsb' 64 1 bits) ++ BitVec.extractLsb' 0 1 bits
  digit * (BitVec.extractLsb' 64 1 d ++ d) +
    (BitVec.extractLsb' 129 1 bits ++ BitVec.extractLsb' 65 65 bits)

private theorem unpack_repack (product : BitVec 66) (sign : BitVec 1) (low : BitVec 63) :
    unpackMultiply (((BitVec.extractLsb' 1 65 product ++ sign) ++
      BitVec.extractLsb' 0 1 product) ++ low) = product ++ low := by
  unfold unpackMultiply
  bv_decide

/-- Removing the separate sign digit exposes the ordinary concatenation of
    the updated accumulator with the shifted multiplier. -/
theorem unpack_multiply_advance (bits : BitVec 130) (d : BitVec 65)
    (count : BitVec 7) (negative : BitVec 1) :
    unpackMultiply (multiplyAdvance bits d count negative) =
      multiplyAccumulator bits d ++ BitVec.extractLsb' 1 63 bits := by
  exact unpack_repack _ _ _

private theorem repack_sign (product : BitVec 66) (sign : BitVec 1) (low : BitVec 63) :
    BitVec.extractLsb' 64 1 (((BitVec.extractLsb' 1 65 product ++ sign) ++
      BitVec.extractLsb' 0 1 product) ++ low) = sign := by
  bv_decide

/-- The sign digit is zero until the edge immediately preceding the final
    multiplication digit, where it becomes the captured correction bit. -/
theorem multiply_sign_digit (bits : BitVec 130) (d : BitVec 65)
    (count : BitVec 7) (negative : BitVec 1) :
    BitVec.extractLsb' 64 1 (multiplyAdvance bits d count negative) =
      (if count = 62#7 then 1#1 else 0#1) &&& negative := by
  exact repack_sign _ _ _

/-- A captured operand starts with a zero accumulator and no sign digit. -/
theorem unpack_initial (a : BitVec 64) :
    unpackMultiply (0#66 ++ a) = 0#65 ++ a := by
  unfold unpackMultiply
  bv_decide

/-- Ordinary digits contribute either zero or one copy of the multiplicand. -/
theorem multiply_unsigned_digit (bits : BitVec 130) (d : BitVec 65)
    (unsignedDigit : BitVec.extractLsb' 64 1 bits = 0#1) :
    multiplyAccumulator bits d =
      (if BitVec.extractLsb' 0 1 bits = 1#1 then d.signExtend 66 else 0#66) +
      (BitVec.extractLsb' 65 65 bits).signExtend 66 := by
  unfold multiplyAccumulator
  rw [unsignedDigit]
  by_cases low : BitVec.extractLsb' 0 1 bits = 1#1
  · simp only [low, if_pos]
    bv_decide
  · have zero : BitVec.extractLsb' 0 1 bits = 0#1 := by bv_decide
    simp only [zero, low, if_neg]
    bv_decide

/-- The final signed digit has weight minus one when its low bit is one. -/
theorem multiply_negative_digit (bits : BitVec 130) (d : BitVec 65)
    (signedDigit : BitVec.extractLsb' 64 1 bits = 1#1)
    (low : BitVec.extractLsb' 0 1 bits = 1#1) :
    multiplyAccumulator bits d =
      (BitVec.extractLsb' 65 65 bits).signExtend 66 - d.signExtend 66 := by
  unfold multiplyAccumulator
  rw [signedDigit, low]
  bv_decide

#print axioms multiply_unsigned_digit
#print axioms multiply_negative_digit
#print axioms unpack_multiply_advance
#print axioms multiply_sign_digit
end HierarchicalMulDiv
