import Proofs.MulDivMulSignedRun

namespace MulDivMultiply
open nMulDiv

theorem decode_signed_product (a : BitVec 64) (b p result : Int) (q : Nat)
    (size : q < 2^63)
    (balance : 9223372036854775808 * p + q = a.toNat + 18446744073709551616 * b * q)
    (edge : 2 * result + (if a.msb then 1 else 0) =
      p + 18446744073709551616 * ((if a.msb then -1 else 0) * b)) :
    result = a.toInt * b := by
  have range := a.isLt
  rw [Int.mul_assoc] at balance
  cases signBit : a.msb with
  | false =>
    have small := BitVec.toNat_lt_of_msb_false signBit
    have consumed : (q : Int) = a.toNat := by omega
    rw [consumed] at balance
    simp only [signBit, Bool.false_eq_true, if_false, Int.zero_mul, Int.add_zero] at edge
    rw [BitVec.toInt_eq_toNat_of_msb signBit, Int.mul_comm (a.toNat : Int) b]
    omega
  | true =>
    have large := BitVec.le_toNat_of_msb_true signBit
    have consumed : (q : Int) = (a.toNat : Int) - 9223372036854775808 := by omega
    rw [consumed, Int.mul_sub, Int.mul_sub] at balance
    simp only [signBit, if_true, Int.neg_one_mul] at edge
    rw [BitVec.toInt_eq_msb_cond]
    simp only [signBit, if_true]
    rw [Int.sub_mul, Int.mul_comm (a.toNat : Int) b]
    have commute : b * 9223372036854775808 = 9223372036854775808 * b := Int.mul_comm _ _
    rw [commute] at balance
    omega

/-- The actual 64-edge signed-high multiply loop computes the exact signed
product, including the final multiplier bit's negative weight. -/
theorem signed_product (s : State) (inputs : Nat → Inputs) (a : BitVec 64) (b : BitVec 65)
    (state : s.r0_nstate = 2) (count : s.r3_ncount = 0)
    (divisor : s.r7_ndivisor = b) (initialSign : sign s = 0)
    (initial : packed s = 0#65 ++ a)
    (negative : s.r4_nneg_5Fout = BitVec.ofBool a.msb)
    (bBound : -18446744073709551616 < b.toInt ∧ b.toInt < 18446744073709551616)
    (reset : ∀ t, t < 64 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 64 → (inputs t).nio_5Fkill = 0) :
    (packed (run s inputs 64)).toInt = a.toInt * b.toInt := by
  have resets : ∀ t, t < 63 → (inputs t).nreset = 0 := fun t h => reset t (by omega)
  have kills : ∀ t, t < 63 → (inputs t).nio_5Fkill = 0 := fun t h => kill t (by omega)
  rcases signed_prefix 63 s inputs a b (by decide) state count divisor initialSign initial
    bBound resets kills with ⟨captured, accBound, q, size, balance⟩
  have countNat : s.r3_ncount.toNat = 0 := congrArg BitVec.toNat count
  have control := compute_prefix 63 s inputs state (by omega) resets kills
  have coefficient := last_signed_digit s inputs a state count initial negative resets kills
  have coefficientCases :
      ((sign (run s inputs 63) ++ (packed (run s inputs 63)).extractLsb' 0 1) : BitVec 2).toInt = -1 ∨
      ((sign (run s inputs 63) ++ (packed (run s inputs 63)).extractLsb' 0 1) : BitVec 2).toInt = 0 ∨
      ((sign (run s inputs 63) ++ (packed (run s inputs 63)).extractLsb' 0 1) : BitVec 2).toInt = 1 := by
    rw [coefficient]
    cases a.msb <;> simp
  have edge := signed_step_balance (packed (run s inputs 63)) b (sign (run s inputs 63))
    coefficientCases bBound accBound
  have bit := bit_run 63 s inputs 0 state (by omega) (by decide) resets kills
  rw [initial] at bit
  have original : (lowWord (packed (run s inputs 63))).getLsbD 0 = a.msb := by
    simpa only [lowWord, BitVec.getLsbD_extractLsb', show 0 < 64 by decide, Bool.true_and,
      Nat.zero_add, BitVec.getLsbD_append, show 63 < 64 by decide, if_true,
      BitVec.msb_eq_getLsbD_last] using bit
  rw [original, coefficient] at edge
  have next : packed (run s inputs 64) =
      multiplyStep (packed (run s inputs 63)) b (sign (run s inputs 63)) := by
    change packed (step (run s inputs 63) (inputs 63)) = _
    rw [compute_datapath _ _ control.1, captured]
  rw [← next] at edge
  exact decode_signed_product a b.toInt (packed (run s inputs 63)).toInt
    (packed (run s inputs 64)).toInt q size balance edge

end MulDivMultiply
