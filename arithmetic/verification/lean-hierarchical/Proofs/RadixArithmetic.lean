import Proofs.RadixExecution

namespace HierarchicalRadix

def quotientDigits (bits : BitVec 129) (divisor : BitVec 64) : Nat → Nat
  | 0 => 0
  | n + 1 => 2 * quotientDigits bits divisor n +
      selectedBit (advanceMany divisor n bits) divisor

theorem iterated_bound (bits : BitVec 129) (divisor : BitVec 64)
    (bound : candidate bits < 2 * divisor.toNat) (n : Nat) :
    candidate (advanceMany divisor n bits) < 2 * divisor.toNat := by
  induction n with
  | zero => exact bound
  | succ n ih => exact advance_bound _ divisor ih

/-- Accumulating quotient digits preserves the complete unbounded identity. -/
theorem iterated_balance (bits : BitVec 129) (divisor : BitVec 64)
    (bound : candidate bits < 2 * divisor.toNat) (n : Nat) :
    (advanceMany divisor n bits).toNat +
        quotientDigits bits divisor n * divisor.toNat * 36893488147419103232 =
      2 ^ n * bits.toNat + quotientDigits bits divisor n := by
  induction n with
  | zero => simp [advanceMany, quotientDigits]
  | succ n ih =>
    have digit := advance_balance (advanceMany divisor n bits) divisor
      (iterated_bound bits divisor bound n)
    simp only [advanceMany, quotientDigits, Nat.pow_succ]
    rw [Nat.add_mul, Nat.add_mul]
    simp only [Nat.mul_assoc] at ih digit ⊢
    rw [Nat.mul_left_comm (2 ^ n) 2 bits.toNat]
    omega

theorem quotientDigits_lt (bits : BitVec 129) (divisor : BitVec 64) (n : Nat) :
    quotientDigits bits divisor n < 2 ^ n := by
  induction n with
  | zero => simp [quotientDigits]
  | succ n ih =>
    have digit : selectedBit (advanceMany divisor n bits) divisor ≤ 1 := by
      unfold selectedBit
      split <;> omega
    simp only [quotientDigits, Nat.pow_succ]
    omega

/-- Once the initial shift and iteration count account for all 64 dividend
    bits, the physical output slices are the Euclidean quotient and remainder. -/
theorem completed_arithmetic (bits : BitVec 129) (divisor : BitVec 64)
    (dividend n : Nat) (bound : candidate bits < 2 * divisor.toNat)
    (iterations : n ≤ 64)
    (scaled : 2 ^ n * bits.toNat = dividend * 36893488147419103232) :
    (BitVec.extractLsb' 0 64 (advanceMany divisor n bits)).toNat = dividend / divisor.toNat ∧
    (BitVec.extractLsb' 65 64 (advanceMany divisor n bits)).toNat = dividend % divisor.toNat := by
  let q := quotientDigits bits divisor n
  let result := advanceMany divisor n bits
  have balance := iterated_balance bits divisor bound n
  rw [scaled] at balance
  have qBound : q < 18446744073709551616 := by
    have power := Nat.pow_le_pow_right (by decide : 0 < 2) iterations
    have digits := quotientDigits_lt bits divisor n
    change q < 2 ^ 64
    exact Nat.lt_of_lt_of_le digits power
  have resultBound := iterated_bound bits divisor bound n
  rw [candidate_value] at resultBound
  have positive : 0 < divisor.toNat := by omega
  have identity : dividend = q * divisor.toNat + result.toNat / 36893488147419103232 := by
    change result.toNat + q * divisor.toNat * 36893488147419103232 =
      dividend * 36893488147419103232 + q at balance
    omega
  have remainderBound : result.toNat / 36893488147419103232 < divisor.toNat := by
    change result.toNat / 18446744073709551616 < 2 * divisor.toNat at resultBound
    omega
  have quotient : q = dividend / divisor.toNat := by
    have divided := congrArg (fun value => value / divisor.toNat) identity
    dsimp only at divided
    rw [Nat.mul_comm q divisor.toNat, Nat.mul_add_div positive,
      Nat.div_eq_of_lt remainderBound, Nat.add_zero] at divided
    exact divided.symm
  have remainder : result.toNat / 36893488147419103232 = dividend % divisor.toNat := by
    have reduced := congrArg (fun value => value % divisor.toNat) identity
    simpa [Nat.add_mod, Nat.mod_eq_of_lt remainderBound] using reduced.symm
  have width := result.isLt
  constructor
  · rw [← quotient]
    change (BitVec.extractLsb' 0 64 result).toNat = q
    simp only [BitVec.extractLsb'_toNat]
    change result.toNat % 18446744073709551616 = q
    change result.toNat + q * divisor.toNat * 36893488147419103232 =
      dividend * 36893488147419103232 + q at balance
    omega
  · rw [← remainder]
    change (BitVec.extractLsb' 65 64 result).toNat = result.toNat / 36893488147419103232
    simp only [BitVec.extractLsb'_toNat]
    omega

#print axioms completed_arithmetic
#print axioms iterated_balance
end HierarchicalRadix
