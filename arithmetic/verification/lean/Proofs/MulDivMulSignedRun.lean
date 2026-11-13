import Proofs.MulDivMulInt

namespace MulDivMultiply
open nMulDiv

theorem unsigned_coefficient (p : BitVec 129) :
    ((0#1 ++ p.extractLsb' 0 1) : BitVec 2).toInt = (digit p : Int) := by
  have bit : p.extractLsb' 0 1 = BitVec.ofBool ((lowWord p).getLsbD 0) := by
    simp only [lowWord]
    bv_decide
  rw [bit]
  unfold digit
  cases h : (lowWord p).getLsbD 0 <;> rfl

theorem advance_integer_balance (scale z next bit b consumed a : Int)
    (edge : 2 * next + bit = z + 18446744073709551616 * b * bit)
    (balance : scale * z + consumed = a + 18446744073709551616 * b * consumed) :
    (2 * scale) * next + (consumed + bit * scale) =
      a + 18446744073709551616 * b * (consumed + bit * scale) := by
  calc
    _ = scale * (2 * next + bit) + consumed := by simp only [Int.mul_add]; ac_rfl
    _ = scale * (z + 18446744073709551616 * b * bit) + consumed := by rw [edge]
    _ = (scale * z + consumed) + 18446744073709551616 * b * (bit * scale) := by
      simp only [Int.mul_add]
      ac_rfl
    _ = a + 18446744073709551616 * b * consumed +
        18446744073709551616 * b * (bit * scale) := by rw [balance]
    _ = _ := by simp only [Int.mul_add, Int.add_assoc]

/-- The first 63 bits have positive weight, even when the captured
multiplicand is signed. The packed invariant is over unbounded integers. -/
theorem signed_prefix_from_count (n : Nat) (s : State) (inputs : Nat → Inputs) (a : BitVec 64) (b : BitVec 65)
    (limit : s.r3_ncount.toNat + n ≤ 63) (state : s.r0_nstate = 2)
    (divisor : s.r7_ndivisor = b) (initialSign : sign s = 0) (initial : packed s = 0#65 ++ a)
    (bBound : -18446744073709551616 < b.toInt ∧ b.toInt < 18446744073709551616)
    (reset : ∀ t, t < n → (inputs t).nreset = 0)
    (kill : ∀ t, t < n → (inputs t).nio_5Fkill = 0) :
    (run s inputs n).r7_ndivisor = b ∧
    (-18446744073709551616 < ((packed (run s inputs n)).extractLsb' 64 65).toInt ∧
      ((packed (run s inputs n)).extractLsb' 64 65).toInt < 18446744073709551616) ∧
    ∃ consumed : Nat, consumed < 2^n ∧
      (2^n : Nat) * (packed (run s inputs n)).toInt + consumed =
        (a.toNat : Int) + 18446744073709551616 * b.toInt * consumed := by
  induction n with
  | zero =>
    refine ⟨divisor, ?_, 0, by decide, ?_⟩
    · have high : (0#65 ++ a).extractLsb' 64 65 = 0#65 := by bv_decide
      change -18446744073709551616 < ((packed s).extractLsb' 64 65).toInt ∧ ((packed s).extractLsb' 64 65).toInt < 18446744073709551616
      rw [initial, high]
      decide
    · change (2^0 : Nat) * (packed s).toInt + (0 : Nat) = _
      rw [initial, BitVec.toInt_append]
      simp
  | succ n ih =>
    have prior := ih (by omega) (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
    rcases prior with ⟨priorDivisor, accumulatorBound, consumed, size, balance⟩
    have control := compute_prefix n s inputs state (by omega)
      (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
    have currentSign := prefix_sign_from_count n s inputs state initialSign (by omega)
      (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
    let p := packed (run s inputs n)
    let bit := digit p
    have bits : bit = 0 ∨ bit = 1 := by unfold bit digit; split <;> simp
    have coefficient := unsigned_coefficient p
    have coefficientCases : ((0#1 ++ p.extractLsb' 0 1) : BitVec 2).toInt = -1 ∨
        ((0#1 ++ p.extractLsb' 0 1) : BitVec 2).toInt = 0 ∨
        ((0#1 ++ p.extractLsb' 0 1) : BitVec 2).toInt = 1 := by
      rw [coefficient]
      change (bit : Int) = -1 ∨ (bit : Int) = 0 ∨ (bit : Int) = 1
      rcases bits with h | h <;> simp [h]
    have next : packed (step (run s inputs n) (inputs n)) = multiplyStep p b 0 := by
      rw [compute_datapath _ _ control.1, priorDivisor, currentSign]
    have edge := signed_step_balance p b 0 coefficientCases bBound accumulatorBound
    have bitCast : (if (lowWord p).getLsbD 0 then (1 : Int) else 0) = (bit : Int) := by
      unfold bit digit
      split <;> rfl
    rw [bitCast] at edge
    have coefficientZero : (((0 : BitVec 1) ++ p.extractLsb' 0 1) : BitVec 2).toInt = (digit p : Int) := coefficient
    rw [coefficientZero] at edge
    have localEdge : 2 * (multiplyStep p b 0).toInt + (bit : Int) =
        p.toInt + 18446744073709551616 * b.toInt * (bit : Int) := by
      simpa only [Int.mul_comm (digit p : Int) b.toInt, Int.mul_assoc] using edge
    have nextBalance := advance_integer_balance (2^n : Nat) p.toInt (multiplyStep p b 0).toInt
      bit b.toInt consumed a.toNat localEdge balance
    change (step (run s inputs n) (inputs n)).r7_ndivisor = b ∧ _
    refine ⟨(preserve_operands _ _ control.1).1.trans priorDivisor, ?_, consumed + bit * 2^n, ?_, ?_⟩
    · change -18446744073709551616 < ((packed (step (run s inputs n) (inputs n))).extractLsb' 64 65).toInt ∧ ((packed (step (run s inputs n) (inputs n))).extractLsb' 64 65).toInt < 18446744073709551616
      rw [next]
      exact signed_accumulator_bound p b 0 coefficientCases bBound accumulatorBound
    · rw [Nat.pow_succ]
      rcases bits with h | h <;> rw [h] <;> simp only [Nat.zero_mul, Nat.one_mul, Nat.add_zero] <;> omega
    · change (2^(n+1) : Nat) * (packed (step (run s inputs n) (inputs n))).toInt + _ = _
      rw [next]
      simpa only [Nat.pow_succ, Int.natCast_add, Int.natCast_mul, show ((2 : Nat) : Int) = 2 from rfl,
        Int.mul_comm (2^n : Nat) 2] using nextBalance


theorem signed_prefix (n : Nat) (s : State) (inputs : Nat → Inputs) (a : BitVec 64) (b : BitVec 65)
    (limit : n ≤ 63) (state : s.r0_nstate = 2) (count : s.r3_ncount = 0)
    (divisor : s.r7_ndivisor = b) (initialSign : sign s = 0) (initial : packed s = 0#65 ++ a)
    (bBound : -18446744073709551616 < b.toInt ∧ b.toInt < 18446744073709551616)
    (reset : ∀ t, t < n → (inputs t).nreset = 0)
    (kill : ∀ t, t < n → (inputs t).nio_5Fkill = 0) :
    (run s inputs n).r7_ndivisor = b ∧
    (-18446744073709551616 < ((packed (run s inputs n)).extractLsb' 64 65).toInt ∧
      ((packed (run s inputs n)).extractLsb' 64 65).toInt < 18446744073709551616) ∧
    ∃ consumed : Nat, consumed < 2^n ∧
      (2^n : Nat) * (packed (run s inputs n)).toInt + consumed =
        (a.toNat : Int) + 18446744073709551616 * b.toInt * consumed := by
  have countNat : s.r3_ncount.toNat = 0 := congrArg BitVec.toNat count
  exact signed_prefix_from_count n s inputs a b (by omega) state divisor initialSign initial bBound reset kill

end MulDivMultiply
