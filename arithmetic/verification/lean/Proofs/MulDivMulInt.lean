import Proofs.MulDivMulBits

namespace MulDivMultiply

/-- The signed 66-bit multiply/add is exact for coefficients -1, 0, and 1.
Both operands stay strictly inside the 65-bit signed endpoints. -/
theorem signed_partial_sum (coefficient : BitVec 2) (b accumulator : BitVec 65)
    (digit : coefficient.toInt = -1 ∨ coefficient.toInt = 0 ∨ coefficient.toInt = 1)
    (bBound : -18446744073709551616 < b.toInt ∧ b.toInt < 18446744073709551616)
    (aBound : -18446744073709551616 < accumulator.toInt ∧ accumulator.toInt < 18446744073709551616) :
    (coefficient.signExtend 66 * b.signExtend 66 + accumulator.signExtend 66).toInt =
      coefficient.toInt * b.toInt + accumulator.toInt := by
  rw [BitVec.toInt_add, BitVec.toInt_mul,
    BitVec.toInt_signExtend_of_le (by decide : 2 ≤ 66),
    BitVec.toInt_signExtend_of_le (by decide : 65 ≤ 66),
    BitVec.toInt_signExtend_of_le (by decide : 65 ≤ 66)]
  have productBound : -18446744073709551616 < coefficient.toInt * b.toInt ∧
      coefficient.toInt * b.toInt < 18446744073709551616 := by
    rcases digit with h | h | h <;> rw [h] <;>
      simp only [Int.neg_one_mul, Int.zero_mul, Int.one_mul] <;> omega
  have productExact : (coefficient.toInt * b.toInt).bmod (2^66) = coefficient.toInt * b.toInt :=
    Int.bmod_eq_of_le (by omega) (by omega)
  rw [productExact]
  exact Int.bmod_eq_of_le (by omega) (by omega)

theorem packed_int (p : BitVec 129) :
    p.toInt = 18446744073709551616 * (p.extractLsb' 64 65).toInt + (lowWord p).toNat := by
  have split : p = p.extractLsb' 64 65 ++ lowWord p := by simp only [lowWord]; bv_decide
  have value := congrArg BitVec.toInt split
  rw [BitVec.toInt_append] at value
  exact value

private theorem shifted_low (p : BitVec 129) :
    (p.extractLsb' 1 63).toNat = (lowWord p).toNat / 2 := by
  simp only [lowWord, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  omega

theorem signed_step_int (p : BitVec 129) (b : BitVec 65) (negative : BitVec 1)
    (digit : (negative ++ p.extractLsb' 0 1).toInt = -1 ∨
      (negative ++ p.extractLsb' 0 1).toInt = 0 ∨ (negative ++ p.extractLsb' 0 1).toInt = 1)
    (bBound : -18446744073709551616 < b.toInt ∧ b.toInt < 18446744073709551616)
    (aBound : -18446744073709551616 < (p.extractLsb' 64 65).toInt ∧
      (p.extractLsb' 64 65).toInt < 18446744073709551616) :
    (multiplyStep p b negative).toInt = 9223372036854775808 *
      ((negative ++ p.extractLsb' 0 1).toInt * b.toInt + (p.extractLsb' 64 65).toInt) +
      ((lowWord p).toNat / 2 : Nat) := by
  have product := signed_partial_sum (negative ++ p.extractLsb' 0 1) b (p.extractLsb' 64 65)
    digit bBound aBound
  change (stepProduct p b negative).toInt = _ at product
  rw [multiplyStep, BitVec.toInt_append]
  simp only [show (66 == 0) = false from rfl, Bool.false_eq_true, if_false]
  rw [product, shifted_low]
  rfl

/-- The signed arithmetic balance retains the discarded multiplier bit,
including the final negative coefficient. -/
theorem signed_step_balance (p : BitVec 129) (b : BitVec 65) (negative : BitVec 1)
    (digit : (negative ++ p.extractLsb' 0 1).toInt = -1 ∨
      (negative ++ p.extractLsb' 0 1).toInt = 0 ∨ (negative ++ p.extractLsb' 0 1).toInt = 1)
    (bBound : -18446744073709551616 < b.toInt ∧ b.toInt < 18446744073709551616)
    (aBound : -18446744073709551616 < (p.extractLsb' 64 65).toInt ∧
      (p.extractLsb' 64 65).toInt < 18446744073709551616) :
    2 * (multiplyStep p b negative).toInt + (if (lowWord p).getLsbD 0 then 1 else 0) =
      p.toInt + 18446744073709551616 * ((negative ++ p.extractLsb' 0 1).toInt * b.toInt) := by
  rw [signed_step_int p b negative digit bBound aBound]
  have split := packed_int p
  have parity := low_parity (lowWord p)
  cases h : (lowWord p).getLsbD 0 <;>
    simp only [h, Bool.false_eq_true, if_false, if_true] at parity ⊢ <;> omega

private theorem signed_half (value : BitVec 66) :
    value.toInt = 2 * (value.extractLsb' 1 65).toInt + (value.extractLsb' 0 1).toNat := by
  have split : value = value.extractLsb' 1 65 ++ value.extractLsb' 0 1 := by bv_decide
  have result := congrArg BitVec.toInt split
  rw [BitVec.toInt_append] at result
  exact result

/-- A signed shift/add edge preserves the accumulator range needed for the
next edge's no-overflow proof. -/
theorem signed_accumulator_bound (p : BitVec 129) (b : BitVec 65) (negative : BitVec 1)
    (digit : (negative ++ p.extractLsb' 0 1).toInt = -1 ∨
      (negative ++ p.extractLsb' 0 1).toInt = 0 ∨ (negative ++ p.extractLsb' 0 1).toInt = 1)
    (bBound : -18446744073709551616 < b.toInt ∧ b.toInt < 18446744073709551616)
    (aBound : -18446744073709551616 < (p.extractLsb' 64 65).toInt ∧
      (p.extractLsb' 64 65).toInt < 18446744073709551616) :
    -18446744073709551616 < ((multiplyStep p b negative).extractLsb' 64 65).toInt ∧
      ((multiplyStep p b negative).extractLsb' 64 65).toInt < 18446744073709551616 := by
  have projection : (multiplyStep p b negative).extractLsb' 64 65 =
      (stepProduct p b negative).extractLsb' 1 65 := by
    unfold multiplyStep
    generalize stepProduct p b negative = product
    bv_decide
  rw [projection]
  have product := signed_partial_sum (negative ++ p.extractLsb' 0 1) b (p.extractLsb' 64 65)
    digit bBound aBound
  change (stepProduct p b negative).toInt = _ at product
  have split := signed_half (stepProduct p b negative)
  have low := ((stepProduct p b negative).extractLsb' 0 1).isLt
  rcases digit with h | h | h <;> rw [h] at product <;>
    simp only [Int.neg_one_mul, Int.zero_mul, Int.one_mul] at product <;> omega

end MulDivMultiply
