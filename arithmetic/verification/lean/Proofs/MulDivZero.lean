import Proofs.MulDivDivision

namespace MulDivZero
open nMulDiv
open MulDivDivision
open nRadix2Divider (candidate lowCandidate)

private theorem zero_sign (sh : BitVec 129)
    (bound : candidate sh < 18446744073709551616) : signBit sh 0 = 0 := by
  have diff : difference sh 0 = sh.extractLsb' 64 65 := by
    simp only [difference]
    bv_decide
  unfold signBit
  rw [diff]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow, Nat.reducePow]
  simp only [candidate, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.reducePow] at bound
  change (sh.toNat / 18446744073709551616 % 36893488147419103232) /
    18446744073709551616 % 2 = 0
  omega

/-- Before the last zero-divisor iteration, subtraction never borrows. The
packed register therefore shifts left and appends one, without truncation. -/
theorem zero_step_nat (sh : BitVec 129)
    (bound : candidate sh < 18446744073709551616) :
    (divisionStep sh 0).toNat = 2 * sh.toNat + 1 := by
  have low : (difference sh 0).extractLsb' 0 64 = lowCandidate sh := by
    simp only [difference, lowCandidate]
    bv_decide
  have sign := zero_sign sh bound
  have stepEq : divisionStep sh 0 = (lowCandidate sh ++ sh.extractLsb' 0 64) ++ 1#1 := by
    unfold divisionStep
    rw [sign, if_neg (by decide : (0 : BitVec 1) ≠ 1), low]
    rfl
  rw [stepEq, nRadix2Divider.concatenate_step_toNat, nRadix2Divider.lowCandidate_toNat]
  have split := nRadix2Divider.split_shift_toNat sh
  have modulus : candidate sh % 18446744073709551616 = candidate sh := Nat.mod_eq_of_lt bound
  rw [modulus]
  change 2 * (candidate sh * 18446744073709551616 + (sh.extractLsb' 0 64).toNat) + 1 = _
  omega

private theorem packed_zero_step (s : State) (i : Inputs) (state : s.r0_nstate = 3)
    (divisor : s.r7_ndivisor = 0) :
    packed (step s i) = divisionStep (packed s) 0 := by
  unfold packed at ⊢
  rw [compute_datapath _ _ state, divisor]
  change (0#1 ++ divisionStep (packed s) 0).extractLsb' 0 129 = divisionStep (packed s) 0
  generalize divisionStep (packed s) 0 = result
  bv_decide

/-- Exact packed value throughout all 65 actual zero-divisor edges. -/
theorem zero_execution (n : Nat) (s : State) (inputs : Nat → Inputs) (a : BitVec 64)
    (limit : n ≤ 65) (state : s.r0_nstate = 3) (count : s.r3_ncount = 0)
    (divisor : s.r7_ndivisor = 0) (initial : (packed s).toNat = a.toNat)
    (reset : ∀ t, t < n → (inputs t).nreset = 0)
    (kill : ∀ t, t < n → (inputs t).nio_5Fkill = 0) :
    (run s inputs n).r7_ndivisor = 0 ∧
    (packed (run s inputs n)).toNat = a.toNat * 2^n + (2^n - 1) := by
  induction n with
  | zero => simpa [run] using And.intro divisor initial
  | succ n ih =>
    have prior := ih (by omega) (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
    have countNat : s.r3_ncount.toNat = 0 := congrArg BitVec.toNat count
    have control := div_prefix n s inputs state (by omega)
      (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
    have size := a.isLt
    have power : 2^n ≤ 18446744073709551616 :=
      Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : n ≤ 64)
    have positive : 0 < 2^n := Nat.two_pow_pos n
    have upper : (a.toNat + 1) * 2^n ≤ 340282366920938463463374607431768211456 :=
      Nat.mul_le_mul (by omega : a.toNat + 1 ≤ 18446744073709551616) power
    rw [Nat.add_mul, Nat.one_mul] at upper
    have bound : candidate (packed (run s inputs n)) < 18446744073709551616 := by
      rw [nRadix2Divider.candidate_eq_div, prior.2]
      omega
    change (step (run s inputs n) (inputs n)).r7_ndivisor = 0 ∧ _
    constructor
    · rw [divisor_stable _ _ control.1, prior.1]
    · change (packed (step (run s inputs n) (inputs n))).toNat = _
      rw [packed_zero_step _ _ control.1 prior.1, zero_step_nat _ bound, prior.2,
        Nat.pow_succ, ← Nat.mul_assoc]
      omega

theorem zero_magnitudes (s : State) (inputs : Nat → Inputs) (a : BitVec 64)
    (state : s.r0_nstate = 3) (count : s.r3_ncount = 0)
    (divisor : s.r7_ndivisor = 0) (initial : (packed s).toNat = a.toNat)
    (reset : ∀ t, t < 65 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 65 → (inputs t).nio_5Fkill = 0) :
    (packed (run s inputs 65)).extractLsb' 0 64 = BitVec.allOnes 64 ∧
    (packed (run s inputs 65)).extractLsb' 65 64 = a := by
  have result := (zero_execution 65 s inputs a (by decide) state count divisor initial reset kill).2
  have size := a.isLt
  constructor <;> apply BitVec.eq_of_toNat_eq
  · simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero, BitVec.toNat_allOnes]
    rw [result]
    omega
  · simp only [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
    rw [result]
    omega

theorem unsigned_accepted_zero (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (full : (inputs 0).nio_5Freq_5Fbits_5Fdw = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 5 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 7)
    (zero : (inputs 0).nio_5Freq_5Fbits_5Fin2 = 0)
    (reset : ∀ t, t < 66 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 66 → (inputs t).nio_5Fkill = 0) :
    (packed (run s inputs 66)).extractLsb' 0 64 = BitVec.allOnes 64 ∧
    (packed (run s inputs 66)).extractLsb' 65 64 = (inputs 0).nio_5Freq_5Fbits_5Fin1 := by
  have captured := unsigned_capture s (inputs 0) idle valid (reset 0 (by decide)) full operation
  have divisor : (step s (inputs 0)).r7_ndivisor = 0 := by
    rw [captured.2.2.1, zero]
    rfl
  have initial : (packed (step s (inputs 0))).toNat = (inputs 0).nio_5Freq_5Fbits_5Fin1.toNat := by
    rw [captured.2.2.2, BitVec.toNat_append]
    simp
  have result := zero_magnitudes (step s (inputs 0)) (fun t => inputs (t + 1))
    (inputs 0).nio_5Freq_5Fbits_5Fin1 captured.1 captured.2.1 divisor initial
    (fun t h => reset (t + 1) (by omega)) (fun t h => kill (t + 1) (by omega))
  rw [show 66 = 65 + 1 from rfl, MulDivControl.run_from_next]
  exact result

end MulDivZero
