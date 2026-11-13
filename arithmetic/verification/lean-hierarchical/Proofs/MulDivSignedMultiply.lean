import Proofs.MulDivUnsignedMultiply

namespace HierarchicalMulDiv

theorem multiply_sign_before_last (bits : BitVec 130) (d : BitVec 65)
    (negative : BitVec 1) (n : Nat) (before : n < 63)
    (initial : BitVec.extractLsb' 64 1 bits = 0#1) :
    BitVec.extractLsb' 64 1 (multiplyMany d negative 0 n bits) = 0#1 := by
  cases n with
  | zero => exact initial
  | succ n =>
    rw [multiplyMany, multiply_sign_digit]
    have notLast : BitVec.ofNat 7 (0 + n) ≠ 62#7 := by
      intro h
      have value := congrArg BitVec.toNat h
      simp at value
      omega
    simp only [Nat.zero_add] at notLast
    simp [notLast]

/-- Inserting the next sign digit does not affect the current unpacked value. -/
theorem unpack_sign_independent (bits : BitVec 130) (d : BitVec 65)
    (count : BitVec 7) (negative : BitVec 1) :
    unpackMultiply (multiplyAdvance bits d count negative) =
      unpackMultiply (multiplyAdvance bits d count 0#1) := by
  rw [unpack_multiply_advance, unpack_multiply_advance]

/-- All but the last multiplication edge share the same recurrence regardless
    of the final sign correction. This also permits signed multiplicands. -/
theorem signed_multiply_prefix (bits : BitVec 130) (d : BitVec 65)
    (negative : BitVec 1) (n : Nat) (within : n ≤ 63)
    (initial : BitVec.extractLsb' 64 1 bits = 0#1) :
    unpackMultiply (multiplyMany d negative 0 n bits) =
      unsignedMultiplyMany d n (unpackMultiply bits) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [multiplyMany, unpack_sign_independent,
      unsigned_multiply_step _ _ _ (multiply_sign_before_last bits d negative n (by omega) initial),
      ih (by omega)]
    rfl

/-- The final edge reads precisely the captured sign correction bit. -/
theorem multiply_final_sign (bits : BitVec 130) (d : BitVec 65) (negative : BitVec 1) :
    BitVec.extractLsb' 64 1 (multiplyMany d negative 0 63 bits) = negative := by
  rw [multiplyMany, multiply_sign_digit]
  change (if 62#7 = 62#7 then 1#1 else 0#1) &&& negative = negative
  bv_decide

theorem multiply_sign_before_final (bits : BitVec 130) (d : BitVec 65)
    (negative : BitVec 1) (start n : Nat) (before : start + n < 63)
    (initial : BitVec.extractLsb' 64 1 bits = 0#1) :
    BitVec.extractLsb' 64 1 (multiplyMany d negative start n bits) = 0#1 := by
  cases n with
  | zero => exact initial
  | succ n =>
    rw [multiplyMany, multiply_sign_digit]
    have notLast : BitVec.ofNat 7 (start + n) ≠ 62#7 := by
      intro h
      have value := congrArg BitVec.toNat h
      simp at value
      omega
    simp [notLast]

/-- Word multiplication starts at count 32 but shares the same ordinary-digit
    recurrence until the final sign digit. -/
theorem signed_multiply_prefix_from (bits : BitVec 130) (d : BitVec 65)
    (negative : BitVec 1) (start n : Nat) (within : start + n ≤ 63)
    (initial : BitVec.extractLsb' 64 1 bits = 0#1) :
    unpackMultiply (multiplyMany d negative start n bits) =
      unsignedMultiplyMany d n (unpackMultiply bits) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [multiplyMany, unpack_sign_independent,
      unsigned_multiply_step _ _ _ (multiply_sign_before_final bits d negative start n (by omega) initial),
      ih (by omega)]
    rfl

#print axioms signed_multiply_prefix_from
#print axioms signed_multiply_prefix
#print axioms multiply_final_sign
end HierarchicalMulDiv
