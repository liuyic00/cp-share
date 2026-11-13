import Proofs.MulDivUnsignedMultiply

namespace HierarchicalMulDiv

theorem unsigned_value_bound (bits : BitVec 129)
    (bounded : BitVec.extractLsb' 128 1 bits = 0#1) : bits.toNat < 2 ^ 128 := by
  have top := congrArg BitVec.toNat bounded
  simp at top
  have width := bits.isLt
  omega

/-- The wide addition has no overflow, so the bitvector operation admits an
    exact natural-number interpretation before division by two. -/
theorem unsigned_step_value (bits : BitVec 129) (d : BitVec 64)
    (bounded : BitVec.extractLsb' 128 1 bits = 0#1) :
    (unsignedMultiplyAdvance bits (0#1 ++ d)).toNat =
      (bits.toNat + (if BitVec.extractLsb' 0 1 bits = 1#1 then d.toNat * 2 ^ 64 else 0)) / 2 := by
  have width := unsigned_value_bound bits bounded
  have divisorWidth := d.isLt
  rw [unsigned_add_shift bits d bounded]
  by_cases low : BitVec.extractLsb' 0 1 bits = 1#1
  all_goals simp only [low, if_pos, if_neg]
  all_goals simp [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight,
    BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.mod_eq_of_lt, width] <;> omega

/-- Each consumed bit adds its multiplicand contribution at the fixed high
    position of the shift register. -/
theorem unsigned_step_linear (bits : BitVec 129) (d : BitVec 64)
    (bounded : BitVec.extractLsb' 128 1 bits = 0#1) :
    (unsignedMultiplyAdvance bits (0#1 ++ d)).toNat = bits.toNat / 2 +
      (if BitVec.extractLsb' 0 1 bits = 1#1 then d.toNat * 2 ^ 63 else 0) := by
  rw [unsigned_step_value bits d bounded]
  split <;> omega

theorem unsigned_step_shiftAdd (bits : BitVec 129) (d : BitVec 64)
    (bounded : BitVec.extractLsb' 128 1 bits = 0#1) :
    (unsignedMultiplyAdvance bits (0#1 ++ d)).toNat =
      HierarchicalMultiply.shiftAdd (d.toNat * 2 ^ 63) bits.toNat := by
  rw [unsigned_step_linear bits d bounded]
  unfold HierarchicalMultiply.shiftAdd
  by_cases low : BitVec.extractLsb' 0 1 bits = 1#1
  · have digit : bits.toNat % 2 = 1 := by
      have h := congrArg BitVec.toNat low
      simpa using h
    simp [low, digit]
  · have digit : bits.toNat % 2 = 0 := by
      have notOne : bits.toNat % 2 ≠ 1 := by
        intro h
        apply low
        apply BitVec.eq_of_toNat_eq
        simpa using h
      omega
    simp [low, digit]

/-- The exact numeric trajectory of the unsigned hardware recurrence. -/
theorem unsigned_iterations_value (bits : BitVec 129) (d : BitVec 64) (n : Nat)
    (bounded : BitVec.extractLsb' 128 1 bits = 0#1) :
    (unsignedMultiplyMany (0#1 ++ d) n bits).toNat =
      HierarchicalMultiply.shiftAddMany (d.toNat * 2 ^ 63) n bits.toNat := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [unsignedMultiplyMany, unsigned_step_shiftAdd _ d (unsigned_iterations_bound bits d n bounded),
      ih, HierarchicalMultiply.shiftAddMany_succ_end]

/-- After all 64 digits, the packed multiplier contains the exact unsigned
    product, before response-half selection. -/
theorem unsigned_packed_product (a d : BitVec 64) :
    (unpackMultiply (multiplyMany (0#1 ++ d) 0#1 0 64 (0#66 ++ a))).toNat =
      a.toNat * d.toNat := by
  have sign : BitVec.extractLsb' 64 1 (0#66 ++ a) = 0#1 := by bv_decide
  rw [unsigned_multiply_iterations _ _ _ _ sign, unpack_initial]
  have bounded : BitVec.extractLsb' 128 1 (0#65 ++ a) = 0#1 := by bv_decide
  rw [unsigned_iterations_value _ d 64 bounded]
  have initial : (0#65 ++ a).toNat = a.toNat := by rw [HierarchicalRadix.append_value]; simp
  rw [initial, HierarchicalMultiply.shiftAddMany_value 63 64 a.toNat d.toNat (by omega),
    HierarchicalMultiply.digitProduct_complete 64 a.toNat d.toNat a.isLt]
  simp [Nat.div_eq_of_lt a.isLt]

#print axioms unsigned_packed_product
#print axioms unsigned_iterations_value
#print axioms unsigned_step_linear
#print axioms unsigned_step_value
end HierarchicalMulDiv
