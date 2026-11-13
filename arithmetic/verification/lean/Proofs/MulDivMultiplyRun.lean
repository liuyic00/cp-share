import Proofs.MulDivMultiply

namespace MulDivMultiply
open nMulDiv

def lowWord (p : BitVec 129) : BitVec 64 := p.extractLsb' 0 64

def digit (p : BitVec 129) : Nat := if (lowWord p).getLsbD 0 then 1 else 0

private theorem join_nat (a low : BitVec 64) :
    (((0#1 ++ a) ++ low) : BitVec 129).toNat = a.toNat * 18446744073709551616 + low.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt low.isLt, BitVec.toNat_append]
  simp [Nat.shiftLeft_eq]

private theorem canonical (p : BitVec 129)
    (fit : p.toNat < 340282366920938463463374607431768211456) :
    p = (0#1 ++ p.extractLsb' 64 64) ++ lowWord p := by
  have bound : p < 340282366920938463463374607431768211456#129 := by
    change p.toNat < 340282366920938463463374607431768211456
    exact fit
  simp only [lowWord]
  bv_decide

theorem unsigned_edge (s : State) (i : Inputs) (b : BitVec 64)
    (state : s.r0_nstate = 2) (divisor : s.r7_ndivisor = 0#1 ++ b) (unsigned : sign s = 0)
    (fit : (packed s).toNat < 340282366920938463463374607431768211456) :
    (packed (step s i)).toNat < 340282366920938463463374607431768211456 ∧
    2 * (packed (step s i)).toNat + digit (packed s) =
      (packed s).toNat + 18446744073709551616 * b.toNat * digit (packed s) := by
  let accumulator := (packed s).extractLsb' 64 64
  let low := lowWord (packed s)
  have representation : packed s = (0#1 ++ accumulator) ++ low := canonical _ fit
  have next : packed (step s i) = multiplyStep ((0#1 ++ accumulator) ++ low) (0#1 ++ b) 0 := by
    rw [compute_datapath _ _ state, divisor, unsigned, representation]
  have oldNat : (packed s).toNat = accumulator.toNat * 18446744073709551616 + low.toNat :=
    (congrArg BitVec.toNat representation).trans (join_nat accumulator low)
  constructor
  · rw [next]
    exact unsigned_step_fits accumulator b low
  · rw [next, oldNat]
    have balance := unsigned_step_balance accumulator b low
    change 2 * (multiplyStep ((0#1 ++ accumulator) ++ low) (0#1 ++ b) 0).toNat +
      (if low.getLsbD 0 then 1 else 0) = _
    cases h : low.getLsbD 0 <;>
      simpa only [digit, show lowWord (packed s) = low from rfl, h, Bool.false_eq_true,
        if_false, if_true, Nat.mul_zero, Nat.mul_one, Nat.add_zero, Nat.mul_comm b.toNat 18446744073709551616] using balance

/-- Packed multiplication balance over every prefix of the actual unsigned
compute loop. `consumed` is bounded independently of the desired result. -/
theorem unsigned_execution (n : Nat) (s : State) (inputs : Nat → Inputs) (a b : BitVec 64)
    (limit : n ≤ 64) (state : s.r0_nstate = 2) (count : s.r3_ncount = 0)
    (divisor : s.r7_ndivisor = 0#1 ++ b) (unsigned : sign s = 0)
    (negative : s.r4_nneg_5Fout = 0) (initial : (packed s).toNat = a.toNat)
    (reset : ∀ t, t < n → (inputs t).nreset = 0)
    (kill : ∀ t, t < n → (inputs t).nio_5Fkill = 0) :
    sign (run s inputs n) = 0 ∧ (run s inputs n).r7_ndivisor = 0#1 ++ b ∧
    (run s inputs n).r4_nneg_5Fout = 0 ∧
    (packed (run s inputs n)).toNat < 340282366920938463463374607431768211456 ∧
    ∃ consumed, consumed < 2^n ∧
      2^n * (packed (run s inputs n)).toNat + consumed =
        a.toNat + 18446744073709551616 * b.toNat * consumed := by
  induction n with
  | zero =>
    refine ⟨unsigned, divisor, negative, ?_, 0, by decide, ?_⟩
    · change (packed s).toNat < _
      rw [initial]
      have size := a.isLt
      omega
    · simpa [run] using initial
  | succ n ih =>
    have prior := ih (by omega) (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
    rcases prior with ⟨priorSign, priorDivisor, priorNegative, fit, consumed, size, balance⟩
    have countNat : s.r3_ncount.toNat = 0 := congrArg BitVec.toNat count
    have control := compute_prefix n s inputs state (by omega)
      (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
    have stable := preserve_operands (run s inputs n) (inputs n) control.1
    have edge := unsigned_edge (run s inputs n) (inputs n) b control.1 priorDivisor priorSign fit
    have nextSign : sign (step (run s inputs n) (inputs n)) = 0 := by
      rw [inject_sign _ _ control.1, priorNegative]
      split <;> rfl
    let bit := digit (packed (run s inputs n))
    have bitBound : bit = 0 ∨ bit = 1 := by unfold bit digit; split <;> simp
    have nextBalance := advance_balance (2^n) _ _ bit b.toNat consumed a.toNat edge.2 balance
    change sign (step (run s inputs n) (inputs n)) = 0 ∧ _
    refine ⟨nextSign, stable.1.trans priorDivisor, stable.2.1.trans priorNegative,
      edge.1, consumed + bit * 2^n, ?_, ?_⟩
    · rw [Nat.pow_succ]
      rcases bitBound with h | h <;> rw [h] <;> simp only [Nat.zero_mul, Nat.one_mul, Nat.add_zero] <;> omega
    · change 2^(n+1) * (packed (step (run s inputs n) (inputs n))).toNat + _ = _
      simpa only [Nat.pow_succ, Nat.mul_comm (2^n) 2] using nextBalance

/-- All 64 iterations of the actual unsigned multiplier produce the full
128-bit natural-number product, not merely a low-half congruence. -/
theorem unsigned_product (s : State) (inputs : Nat → Inputs) (a b : BitVec 64)
    (state : s.r0_nstate = 2) (count : s.r3_ncount = 0)
    (divisor : s.r7_ndivisor = 0#1 ++ b) (unsigned : sign s = 0)
    (negative : s.r4_nneg_5Fout = 0) (initial : (packed s).toNat = a.toNat)
    (reset : ∀ t, t < 64 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 64 → (inputs t).nio_5Fkill = 0) :
    (packed (run s inputs 64)).toNat = a.toNat * b.toNat := by
  rcases unsigned_execution 64 s inputs a b (by decide) state count divisor unsigned negative initial reset kill with
    ⟨_, _, _, _, consumed, size, balance⟩
  rw [Nat.mul_assoc] at balance
  have aBound := a.isLt
  have consumedValue : consumed = a.toNat := by omega
  rw [consumedValue, Nat.mul_comm b.toNat a.toNat] at balance
  omega

end MulDivMultiply
