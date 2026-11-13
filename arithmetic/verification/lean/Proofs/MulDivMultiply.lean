import Proofs.MulDivControl
import Proofs.MulDivOutput

namespace MulDivMultiply
open nMulDiv

/-- The 129-bit multiply register excludes the separately injected sign bit
at physical bit 64. It consists of a signed accumulator and low multiplier. -/
def packed (s : State) : BitVec 129 :=
  s.r8_nremainder.extractLsb' 65 65 ++ s.r8_nremainder.extractLsb' 0 64

def sign (s : State) : BitVec 1 := s.r8_nremainder.extractLsb' 64 1

def stepProduct (p : BitVec 129) (b : BitVec 65) (negative : BitVec 1) : BitVec 66 :=
  let digit := (negative ++ p.extractLsb' 0 1).signExtend 66
  let accumulator := (p.extractLsb' 64 65).signExtend 66
  digit * b.signExtend 66 + accumulator

def multiplyStep (p : BitVec 129) (b : BitVec 65) (negative : BitVec 1) : BitVec 129 :=
  stepProduct p b negative ++ p.extractLsb' 1 63

private def rawProduct (s : State) : BitVec 66 :=
  ((BitVec.replicate 65 (sign s) ++ s.r8_nremainder.extractLsb' 0 1) *
    (s.r7_ndivisor.extractLsb' 64 1 ++ s.r7_ndivisor)) +
    (s.r8_nremainder.extractLsb' 129 1 ++ s.r8_nremainder.extractLsb' 65 65)

private theorem raw_product (s : State) :
    rawProduct s = stepProduct (packed s) s.r7_ndivisor (sign s) := by
  unfold rawProduct stepProduct
  congr 1
  · congr 1 <;> (try simp only [packed, sign]) <;> bv_decide
  · simp only [packed]
    bv_decide

private theorem physical_edge (s : State) (i : Inputs) (state : s.r0_nstate = 2) :
    (step s i).r8_nremainder =
      (((rawProduct s).extractLsb' 1 65 ++
        (if s.r3_ncount = 62 then s.r4_nneg_5Fout else 0)) ++
        (rawProduct s).extractLsb' 0 1) ++ s.r8_nremainder.extractLsb' 1 63 := by
  simp [step, eval, state, rawProduct, sign]
  generalize ((BitVec.replicate 65 (BitVec.extractLsb' 64 1 s.r8_nremainder) ++
    BitVec.extractLsb' 0 1 s.r8_nremainder) *
    (BitVec.extractLsb' 64 1 s.r7_ndivisor ++ s.r7_ndivisor) +
    (BitVec.extractLsb' 129 1 s.r8_nremainder ++ BitVec.extractLsb' 65 65 s.r8_nremainder)) = product
  bv_decide

/-- Exact refinement of the generated multiply edge. The signed two-bit
coefficient permits the final multiplier bit to have negative weight. -/
theorem compute_datapath (s : State) (i : Inputs) (state : s.r0_nstate = 2) :
    packed (step s i) = multiplyStep (packed s) s.r7_ndivisor (sign s) := by
  change (step s i).r8_nremainder.extractLsb' 65 65 ++
    (step s i).r8_nremainder.extractLsb' 0 64 = _
  rw [physical_edge _ _ state, raw_product]
  unfold multiplyStep
  generalize stepProduct (packed s) s.r7_ndivisor (sign s) = product
  simp only [packed]
  bv_decide

theorem inject_sign (s : State) (i : Inputs) (state : s.r0_nstate = 2) :
    sign (step s i) = if s.r3_ncount = 62 then s.r4_nneg_5Fout else 0 := by
  simp only [sign, step, eval, state]
  bv_decide

theorem preserve_operands (s : State) (i : Inputs) (state : s.r0_nstate = 2) :
    (step s i).r7_ndivisor = s.r7_ndivisor ∧
    (step s i).r4_nneg_5Fout = s.r4_nneg_5Fout ∧
    MulDivOutput.metadata (step s i) = MulDivOutput.metadata s := by
  simp [MulDivOutput.metadata, step, eval, state] <;> bv_decide

/-- With a nonnegative accumulator/divisor and an uninjected sign, the
concrete edge is the ordinary unsigned shift/add step. -/
theorem unsigned_step (a : BitVec 64) (b : BitVec 64) (low : BitVec 64) :
    multiplyStep ((0#1 ++ a) ++ low) (0#1 ++ b) 0 =
      ((if low.getLsbD 0 then (0#2 ++ b) else 0#66) + (0#2 ++ a)) ++ low.extractLsb' 1 63 := by
  unfold multiplyStep stepProduct
  have coefficient : ((0 : BitVec 1) ++ (((0#1 ++ a) ++ low) : BitVec 129).extractLsb' 0 1).signExtend 66 =
      if low.getLsbD 0 then 1#66 else 0#66 := by bv_decide
  rw [coefficient]
  have divisor : (0#1 ++ b).signExtend 66 = 0#2 ++ b := by bv_decide
  have accumulator : ((((0#1 ++ a) ++ low) : BitVec 129).extractLsb' 64 65).signExtend 66 = 0#2 ++ a := by bv_decide
  have data : (((0#1 ++ a) ++ low) : BitVec 129).extractLsb' 1 63 = low.extractLsb' 1 63 := by bv_decide
  rw [divisor, accumulator, data]
  split <;> simp

private theorem extend_nat (x : BitVec 64) : (0#2 ++ x).toNat = x.toNat := by
  rw [BitVec.toNat_append]
  simp

/-- Exact unbounded-natural value of the unsigned shift/add edge; the
66-bit partial sum and 129-bit concatenation do not lose any carry. -/
theorem unsigned_step_nat (a b low : BitVec 64) :
    (multiplyStep ((0#1 ++ a) ++ low) (0#1 ++ b) 0).toNat =
      (a.toNat + (if low.getLsbD 0 then b.toNat else 0)) * 9223372036854775808 + low.toNat / 2 := by
  rw [unsigned_step, BitVec.toNat_append]
  rw [← Nat.shiftLeft_add_eq_or_of_lt (low.extractLsb' 1 63).isLt]
  simp only [Nat.shiftLeft_eq, Nat.reducePow, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]
  have ha := a.isLt
  have hb := b.isLt
  have hl := low.isLt
  cases bit : low.getLsbD 0 <;>
    simp only [Bool.false_eq_true, if_false, if_true, BitVec.toNat_add, extend_nat]
  · change ((0 + a.toNat) % 73786976294838206464) * 9223372036854775808 + low.toNat / 2 % 9223372036854775808 = _
    omega
  · have sumBound : b.toNat + a.toNat < 73786976294838206464 := by omega
    rw [Nat.mod_eq_of_lt sumBound]
    omega

theorem low_parity (low : BitVec 64) :
    low.toNat = 2 * (low.toNat / 2) + (if low.getLsbD 0 then 1 else 0) := by
  have bit : BitVec.ofBool (low.getLsbD 0) = low.extractLsb' 0 1 := by bv_decide
  have value := congrArg BitVec.toNat bit
  rw [BitVec.extractLsb'_toNat] at value
  rw [Nat.shiftRight_zero] at value
  cases h : low.getLsbD 0
  · simp only [h, BitVec.toNat_ofBool] at value
    change 0 = low.toNat % 2 at value
    simp only [Bool.false_eq_true, if_false]
    omega
  · simp only [h, BitVec.toNat_ofBool] at value
    change 1 = low.toNat % 2 at value
    simp only [if_true]
    omega

/-- The exact shift/add balance, including the bit discarded by right shift. -/
theorem unsigned_step_balance (a b low : BitVec 64) :
    2 * (multiplyStep ((0#1 ++ a) ++ low) (0#1 ++ b) 0).toNat +
        (if low.getLsbD 0 then 1 else 0) =
      a.toNat * 18446744073709551616 + low.toNat +
        (if low.getLsbD 0 then b.toNat * 18446744073709551616 else 0) := by
  rw [unsigned_step_nat]
  have parity := low_parity low
  simp only [Nat.mul_comm a.toNat 18446744073709551616,
    Nat.mul_comm b.toNat 18446744073709551616,
    Nat.mul_comm (a.toNat + (if low.getLsbD 0 then b.toNat else 0)) 9223372036854775808]
  cases h : low.getLsbD 0 <;>
    simp only [h, Bool.false_eq_true, if_false, if_true, Nat.add_zero] at parity ⊢ <;> omega

/-- The unsigned accumulator stays at most the captured multiplicand. -/
theorem unsigned_accumulator_bound (a b low : BitVec 64) (bound : a.toNat ≤ b.toNat) :
    ((multiplyStep ((0#1 ++ a) ++ low) (0#1 ++ b) 0).extractLsb' 64 65).toNat ≤ b.toNat := by
  rw [BitVec.extractLsb'_toNat, unsigned_step_nat]
  simp only [Nat.shiftRight_eq_div_pow, Nat.reducePow]
  have ha := a.isLt
  have hb := b.isLt
  have hl := low.isLt
  cases h : low.getLsbD 0 <;> simp only [Bool.false_eq_true, if_false, if_true, Nat.add_zero] <;> omega

/-- The packed unsigned result remains nonnegative as a 129-bit signed value.
This justifies zero-extending the accumulator on the next iteration. -/
theorem unsigned_step_fits (a b low : BitVec 64) :
    (multiplyStep ((0#1 ++ a) ++ low) (0#1 ++ b) 0).toNat <
      340282366920938463463374607431768211456 := by
  rw [unsigned_step_nat]
  have ha := a.isLt
  have hb := b.isLt
  have hl := low.isLt
  cases h : low.getLsbD 0 <;> simp only [Bool.false_eq_true, if_false, if_true, Nat.add_zero] <;> omega

/-- Algebraic induction step for the packed multiplication invariant. The
consumed-bit value grows by `digit * scale` while the scale doubles. -/
theorem advance_balance (scale z next digit b consumed a : Nat)
    (edge : 2 * next + digit = z + 18446744073709551616 * b * digit)
    (balance : scale * z + consumed = a + 18446744073709551616 * b * consumed) :
    (2 * scale) * next + (consumed + digit * scale) =
      a + 18446744073709551616 * b * (consumed + digit * scale) := by
  calc
    _ = scale * (2 * next + digit) + consumed := by
      simp only [Nat.mul_add]
      ac_rfl
    _ = scale * (z + 18446744073709551616 * b * digit) + consumed := by rw [edge]
    _ = (scale * z + consumed) + 18446744073709551616 * b * (digit * scale) := by
      simp only [Nat.mul_add]
      ac_rfl
    _ = a + 18446744073709551616 * b * consumed +
        18446744073709551616 * b * (digit * scale) := by rw [balance]
    _ = _ := by simp only [Nat.mul_add, Nat.add_assoc]

theorem capture_unsigned_high (s : State) (i : Inputs)
    (idle : s.r0_nstate = 0) (valid : i.nio_5Freq_5Fvalid = 1)
    (operation : i.nio_5Freq_5Fbits_5Ffn = 3) (full : i.nio_5Freq_5Fbits_5Fdw = 1)
    (reset : i.nreset = 0) :
    (step s i).r0_nstate = 2 ∧ (step s i).r3_ncount = 0 ∧
    packed (step s i) = 0#65 ++ i.nio_5Freq_5Fbits_5Fin1 ∧
    (step s i).r7_ndivisor = 0#1 ++ i.nio_5Freq_5Fbits_5Fin2 ∧
    sign (step s i) = 0 ∧ (step s i).r4_nneg_5Fout = 0 ∧
    MulDivOutput.metadata (step s i) = (1, i.nio_5Freq_5Fbits_5Ftag, 1) := by
  simp only [step, eval, packed, sign, MulDivOutput.metadata, idle, valid,
    operation, full, reset, Prod.mk.injEq]
  bv_decide

theorem compute_prefix (n : Nat) (s : State) (inputs : Nat → Inputs)
    (state : s.r0_nstate = 2) (remaining : s.r3_ncount.toNat + n < 64)
    (reset : ∀ t, t < n → (inputs t).nreset = 0)
    (kill : ∀ t, t < n → (inputs t).nio_5Fkill = 0) :
    (run s inputs n).r0_nstate = 2 ∧
    (run s inputs n).r3_ncount.toNat = s.r3_ncount.toNat + n := by
  induction n with
  | zero => simpa [run] using state
  | succ n ih =>
    have prior := ih (by omega) (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
    have edge := MulDivControl.mul_edge (run s inputs n) (inputs n) prior.1
      (reset n (by omega)) (kill n (by omega))
    have notLast : (run s inputs n).r3_ncount ≠ 63 := by
      intro eq
      have : (run s inputs n).r3_ncount.toNat = 63 := congrArg BitVec.toNat eq
      omega
    constructor
    · change (step (run s inputs n) (inputs n)).r0_nstate = _
      simpa only [notLast, if_false] using edge.1
    · change (step (run s inputs n) (inputs n)).r3_ncount.toNat = _
      rw [edge.2, BitVec.toNat_add]
      change ((run s inputs n).r3_ncount.toNat + 1) % 128 = _
      omega

end MulDivMultiply
