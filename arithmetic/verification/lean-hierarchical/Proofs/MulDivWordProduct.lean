import Proofs.MulDivSignedProduct

namespace HierarchicalMulDiv

private theorem correction_low (x : BitVec 128) (d : BitVec 65) (sign : BitVec 1) :
    (x - (if sign = 1#1 then d.signExtend 128 <<< 64 else 0#128)).setWidth 64 = x.setWidth 64 := by
  bv_decide

/-- The final sign digit affects only bits above the word multiplier's result
    slice. Its low 64-bit register value follows the common 32-step recurrence. -/
theorem word_iterations_low (bits : BitVec 130) (d : BitVec 65) (negative : BitVec 1)
    (initial : BitVec.extractLsb' 64 1 bits = 0#1) :
    (unpackMultiply (multiplyMany d negative 32 32 bits)).setWidth 64 =
      (unsignedMultiplyMany d 32 (unpackMultiply bits)).setWidth 64 := by
  have correction := multiply_sign_correction (multiplyMany d negative 32 31 bits) d 63#7 negative
  have low := congrArg (fun x : BitVec 128 => x.setWidth 64) correction
  dsimp only at low
  rw [correction_low, signed_multiply_prefix_from bits d negative 32 31 (by omega) initial] at low
  have narrow (x : BitVec 129) : (x.setWidth 128).setWidth 64 = x.setWidth 64 := by bv_decide
  simp only [narrow] at low
  exact low

/-- The common word path retains the upper half of its low register as the
    result; the lower half contains the unconsumed upper operand bits. -/
theorem word_common_value (a : BitVec 64) (d : BitVec 65) :
    (unsignedMultiplyMany d 32 (0#65 ++ a)).toInt =
      (a.toNat : Int) / 2 ^ 32 +
        ((a.toNat : Int) - (a.toNat : Int) / 2 ^ 32 * 2 ^ 32) * d.toInt * 2 ^ 32 := by
  rw [signed_iterations_value]
  have initial : (0#65 ++ a).toInt = (a.toNat : Int) := by
    rw [BitVec.toInt_append]
    simp
  rw [initial, HierarchicalSignedMultiply.shiftAddMany_value 63 32 _ _ (by omega),
    HierarchicalSignedMultiply.digitProduct_value]

/-- The register's word result is extracted using Euclidean integer division,
    which also handles a negative signed accumulator. -/
theorem word_slice_value (x : BitVec 129) :
    BitVec.extractLsb' 32 32 x = BitVec.ofInt 32 (x.toInt / 2 ^ 32) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toInt_eq_toNat_cond]
  simp [Nat.shiftRight_eq_div_pow, BitVec.toNat_ofInt]
  split <;> omega

theorem word_common_product (a : BitVec 64) (d : BitVec 65) :
    BitVec.extractLsb' 32 32 (unsignedMultiplyMany d 32 (0#65 ++ a)) =
      a.setWidth 32 * d.setWidth 32 := by
  rw [word_slice_value, word_common_value,
    Int.add_mul_ediv_right _ _ (by decide : (2 ^ 32 : Int) ≠ 0)]
  have quotient : (a.toNat : Int) / 2 ^ 32 / 2 ^ 32 = 0 := by
    have width := a.isLt
    omega
  rw [quotient, Int.zero_add, BitVec.ofInt_mul]
  have left : BitVec.ofInt 32 ((a.toNat : Int) - (a.toNat : Int) / 2 ^ 32 * 2 ^ 32) = a.setWidth 32 := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_ofInt, BitVec.toNat_setWidth]
    omega
  have right : BitVec.ofInt 32 d.toInt = d.setWidth 32 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toInt_eq_toNat_cond]
    simp [BitVec.toNat_ofInt, BitVec.toNat_setWidth]
    split <;> omega
  rw [left, right]

/-- The actual packed 32-edge datapath contains the low word product in the
    slice selected by the word-mode response logic. -/
theorem word_packed_product (a : BitVec 64) (d : BitVec 65) (negative : BitVec 1) :
    BitVec.extractLsb' 32 32 (multiplyMany d negative 32 32 (0#66 ++ a)) =
      a.setWidth 32 * d.setWidth 32 := by
  have initial : BitVec.extractLsb' 64 1 (0#66 ++ a) = 0#1 := by bv_decide
  have low := word_iterations_low (0#66 ++ a) d negative initial
  rw [unpack_initial] at low
  have slice := congrArg (BitVec.extractLsb' 32 32) low
  have packed (x : BitVec 130) :
      BitVec.extractLsb' 32 32 ((unpackMultiply x).setWidth 64) = BitVec.extractLsb' 32 32 x := by
    unfold unpackMultiply
    bv_decide
  have narrow (x : BitVec 129) :
      BitVec.extractLsb' 32 32 (x.setWidth 64) = BitVec.extractLsb' 32 32 x := by bv_decide
  rw [packed, narrow, word_common_product] at slice
  exact slice

#print axioms word_packed_product
#print axioms word_common_product
#print axioms word_common_value
#print axioms word_slice_value
#print axioms word_iterations_low
end HierarchicalMulDiv
