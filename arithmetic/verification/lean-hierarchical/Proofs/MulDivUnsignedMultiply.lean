import Proofs.MulDivMultiplyPacking
import Proofs.MultiplyArithmetic

namespace HierarchicalMulDiv

/-- The packed sign field remains zero for every unsigned multiplication edge. -/
theorem unsigned_multiply_sign (bits : BitVec 130) (d : BitVec 65) (start n : Nat)
    (initial : BitVec.extractLsb' 64 1 bits = 0#1) :
    BitVec.extractLsb' 64 1 (multiplyMany d 0#1 start n bits) = 0#1 := by
  cases n with
  | zero => exact initial
  | succ n =>
    rw [multiplyMany, multiply_sign_digit]
    simp

/-- Removing the sign field gives the usual add-and-shift recurrence. -/
def unsignedMultiplyAdvance (bits : BitVec 129) (d : BitVec 65) : BitVec 129 :=
  let contribution := if BitVec.extractLsb' 0 1 bits = 1#1 then d.signExtend 66 else 0#66
  let accumulator := (BitVec.extractLsb' 64 65 bits).signExtend 66
  (contribution + accumulator) ++ BitVec.extractLsb' 1 63 bits

theorem unsigned_multiply_step (bits : BitVec 130) (d : BitVec 65) (count : BitVec 7)
    (sign : BitVec.extractLsb' 64 1 bits = 0#1) :
    unpackMultiply (multiplyAdvance bits d count 0#1) =
      unsignedMultiplyAdvance (unpackMultiply bits) d := by
  rw [unpack_multiply_advance, multiply_unsigned_digit bits d sign]
  unfold unsignedMultiplyAdvance unpackMultiply
  bv_decide

def unsignedMultiplyMany (d : BitVec 65) : Nat → BitVec 129 → BitVec 129
  | 0, bits => bits
  | n + 1, bits => unsignedMultiplyAdvance (unsignedMultiplyMany d n bits) d

/-- Every packed hardware iteration corresponds to one arithmetic recurrence
    step; the implementation's count no longer appears in the recurrence. -/
theorem unsigned_multiply_iterations (bits : BitVec 130) (d : BitVec 65) (start n : Nat)
    (initial : BitVec.extractLsb' 64 1 bits = 0#1) :
    unpackMultiply (multiplyMany d 0#1 start n bits) =
      unsignedMultiplyMany d n (unpackMultiply bits) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [multiplyMany, unsigned_multiply_step _ _ _ (unsigned_multiply_sign bits d start n initial), ih]
    rfl

/-- Under the unsigned accumulator bound, the hardware recurrence is exactly
    a wide addition followed by a right shift. The extra width prevents carry
    loss before shifting. -/
theorem unsigned_add_shift (bits : BitVec 129) (d : BitVec 64)
    (bounded : BitVec.extractLsb' 128 1 bits = 0#1) :
    unsignedMultiplyAdvance bits (0#1 ++ d) =
      ((bits.setWidth 130 +
        (if BitVec.extractLsb' 0 1 bits = 1#1 then d.setWidth 130 <<< 64 else 0#130)) >>> 1).setWidth 129 := by
  unfold unsignedMultiplyAdvance
  bv_decide

/-- The accumulator bound is inductive for every 64-bit unsigned divisor. -/
theorem unsigned_accumulator_bound (bits : BitVec 129) (d : BitVec 64)
    (bounded : BitVec.extractLsb' 128 1 bits = 0#1) :
    BitVec.extractLsb' 128 1 (unsignedMultiplyAdvance bits (0#1 ++ d)) = 0#1 := by
  unfold unsignedMultiplyAdvance
  bv_decide

theorem unsigned_iterations_bound (bits : BitVec 129) (d : BitVec 64) (n : Nat)
    (bounded : BitVec.extractLsb' 128 1 bits = 0#1) :
    BitVec.extractLsb' 128 1 (unsignedMultiplyMany (0#1 ++ d) n bits) = 0#1 := by
  induction n with
  | zero => exact bounded
  | succ n ih => exact unsigned_accumulator_bound _ d ih

#print axioms unsigned_add_shift
#print axioms unsigned_iterations_bound
#print axioms unsigned_multiply_iterations
end HierarchicalMulDiv
