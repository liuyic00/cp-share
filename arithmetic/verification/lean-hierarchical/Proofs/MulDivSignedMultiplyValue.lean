import Proofs.MulDivSignedMultiply
import Proofs.SignedMultiplyArithmetic

namespace HierarchicalMulDiv

/-- Sign extension of the accumulator and multiplicand makes the shared
    recurrence an arithmetic shift of a wide signed sum. -/
theorem signed_add_shift (bits : BitVec 129) (d : BitVec 65) :
    unsignedMultiplyAdvance bits d =
      ((bits.signExtend 130 +
        (if BitVec.extractLsb' 0 1 bits = 1#1 then d.signExtend 130 <<< 64 else 0#130)).sshiftRight 1).setWidth 129 := by
  unfold unsignedMultiplyAdvance
  bv_decide

/-- Adding one 65-bit multiplicand to a 65-bit accumulator is exact at 66
    bits, even when either signed operand is negative. -/
theorem accumulator_signed_sum (a d : BitVec 65) :
    (a.signExtend 66 + d.signExtend 66).toInt = a.toInt + d.toInt := by
  have noOverflow : ¬ BitVec.saddOverflow (a.signExtend 66) (d.signExtend 66) := by
    bv_decide
  rw [BitVec.toInt_add_of_not_saddOverflow noOverflow,
    BitVec.toInt_signExtend_of_le (by omega), BitVec.toInt_signExtend_of_le (by omega)]

theorem signed_step_components (bits : BitVec 129) (d : BitVec 65) :
    (unsignedMultiplyAdvance bits d).toInt =
      2 ^ 63 * ((if BitVec.extractLsb' 0 1 bits = 1#1 then d.toInt else 0) +
        (BitVec.extractLsb' 64 65 bits).toInt) + (BitVec.extractLsb' 1 63 bits).toNat := by
  unfold unsignedMultiplyAdvance
  rw [BitVec.toInt_append]
  by_cases low : BitVec.extractLsb' 0 1 bits = 1#1
  · simp only [low, if_pos]
    rw [accumulator_signed_sum]
    simp
  · simp [low, BitVec.toInt_signExtend_of_le (by omega : 65 ≤ 66)]

/-- The current signed register decomposes into its accumulator and the
    unsigned multiplier word. -/
theorem signed_register_components (bits : BitVec 129) :
    bits.toInt = 2 ^ 64 * (BitVec.extractLsb' 64 65 bits).toInt +
      (BitVec.extractLsb' 0 64 bits).toNat := by
  have reconstructed : bits = BitVec.extractLsb' 64 65 bits ++ BitVec.extractLsb' 0 64 bits := by
    bv_decide
  have value := congrArg BitVec.toInt reconstructed
  rw [BitVec.toInt_append] at value
  simpa using value

/-- Integer division is the arithmetic right shift, including negative
    accumulator values. -/
theorem signed_step_value (bits : BitVec 129) (d : BitVec 65) :
    (unsignedMultiplyAdvance bits d).toInt = bits.toInt / 2 +
      (if BitVec.extractLsb' 0 1 bits = 1#1 then d.toInt * 2 ^ 63 else 0) := by
  have components := signed_register_components bits
  have lower : (BitVec.extractLsb' 1 63 bits).toNat =
      (BitVec.extractLsb' 0 64 bits).toNat / 2 := by
    simp [Nat.shiftRight_eq_div_pow]
    omega
  rw [signed_step_components, lower]
  split <;> omega

theorem signed_low_digit (bits : BitVec 129) :
    bits.toInt % 2 = (BitVec.extractLsb' 0 1 bits).toNat := by
  rw [BitVec.toInt_eq_toNat_cond]
  simp
  split <;> omega

theorem signed_step_shiftAdd (bits : BitVec 129) (d : BitVec 65) :
    (unsignedMultiplyAdvance bits d).toInt =
      HierarchicalSignedMultiply.shiftAdd (d.toInt * 2 ^ 63) bits.toInt := by
  rw [signed_step_value]
  unfold HierarchicalSignedMultiply.shiftAdd
  rw [signed_low_digit]
  by_cases low : BitVec.extractLsb' 0 1 bits = 1#1
  · simp [low]
  · have zero : BitVec.extractLsb' 0 1 bits = 0#1 := by bv_decide
    simp [low, zero]

/-- This numeric trajectory admits negative multiplicands and accumulators. -/
theorem signed_iterations_value (bits : BitVec 129) (d : BitVec 65) (n : Nat) :
    (unsignedMultiplyMany d n bits).toInt =
      HierarchicalSignedMultiply.shiftAddMany (d.toInt * 2 ^ 63) n bits.toInt := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [unsignedMultiplyMany, signed_step_shiftAdd, ih,
      HierarchicalSignedMultiply.shiftAddMany_succ_end]

#print axioms signed_iterations_value
#print axioms signed_step_value
#print axioms signed_add_shift
#print axioms accumulator_signed_sum
end HierarchicalMulDiv
