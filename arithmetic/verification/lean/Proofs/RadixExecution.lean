import Proofs.RadixInitialization

namespace nRadix2Divider

/-- Before the last iteration the circuit remains in compute, with the counter
    advanced by exactly the number of edges. -/
theorem compute_prefix (n : Nat) (s : State) (inputs : Nat → Inputs)
    (state : s.r0_nstate = 3) (remaining : s.r9_ncnt_5Fvalue.toNat + n < 64)
    (reset : ∀ t, t < n → (inputs t).nreset = 0) :
    (run s inputs n).r0_nstate = 3 ∧
    (run s inputs n).r9_ncnt_5Fvalue.toNat = s.r9_ncnt_5Fvalue.toNat + n := by
  induction n with
  | zero => simpa [run] using state
  | succ n ih =>
      have h := ih (by omega) (by intro t ht; apply reset; omega)
      have r := reset n (by omega)
      have less : (run s inputs n).r9_ncnt_5Fvalue.toNat < 63 := by omega
      have notLast : (run s inputs n).r9_ncnt_5Fvalue ≠ 63 := by
        intro eq
        rw [eq] at less
        contradiction
      change (step (run s inputs n) (inputs n)).r0_nstate = 3 ∧ _
      constructor
      · rw [compute_state _ _ h.1 r, if_neg notLast]
      · change (step (run s inputs n) (inputs n)).r9_ncnt_5Fvalue.toNat = _
        rw [compute_count _ _ h.1 r, BitVec.toNat_add]
        change ((run s inputs n).r9_ncnt_5Fvalue.toNat + 1) % 64 = _
        omega

/-- The actual circuit preserves the packed arithmetic invariant over every
    prefix of its compute execution, including the edge that enters finish.
    `q` is the accumulated quotient, with a proved bit-width bound. -/
theorem compute_execution (n : Nat) (s : State) (inputs : Nat → Inputs)
    (state : s.r0_nstate = 3) (remaining : s.r9_ncnt_5Fvalue.toNat + n ≤ 64)
    (reset : ∀ t, t < n → (inputs t).nreset = 0)
    (initialBound : candidate s.r2_nshiftReg < 2 * s.r5_nbReg.toNat) :
    let final := run s inputs n
    final.r5_nbReg = s.r5_nbReg ∧
    candidate final.r2_nshiftReg < 2 * s.r5_nbReg.toNat ∧
    ∃ q, q < 2^n ∧
      final.r2_nshiftReg.toNat + 36893488147419103232 * s.r5_nbReg.toNat * q =
        2^n * s.r2_nshiftReg.toNat + q := by
  induction n with
  | zero =>
      refine ⟨rfl, initialBound, 0, by decide, ?_⟩
      simp [run]
  | succ n ih =>
      have prior := ih (by omega) (by intro t ht; apply reset; omega)
      rcases prior with ⟨divisor, bound, q, size, balance⟩
      have control := compute_prefix n s inputs state (by omega)
        (by intro t ht; apply reset; omega)
      let current := run s inputs n
      let bit := (quotientBit current.r2_nshiftReg current.r5_nbReg).toNat
      have localBound : candidate current.r2_nshiftReg < 2 * current.r5_nbReg.toNat := by
        change candidate (run s inputs n).r2_nshiftReg < _
        rw [divisor]
        exact bound
      have positive : 0 < current.r5_nbReg.toNat := by omega
      have bitBound : bit ≤ 1 := by
        dsimp [bit]
        rw [quotientBit_correct]
        exact (RestoringDivision.restore_correct _ _ positive localBound).2.2
      have localBalance : current.r2_nshiftReg.toNat +
          36893488147419103232 * current.r5_nbReg.toNat * q =
            2^n * s.r2_nshiftReg.toNat + q := by
        change (run s inputs n).r2_nshiftReg.toNat + _ = _
        rw [divisor]
        exact balance
      have nextBalance := compute_preserves_balance current (inputs n) q
        (2^n * s.r2_nshiftReg.toNat) control.1 localBound localBalance
      have nextDivisor := (compute_preserves_captured current (inputs n) control.1).1
      have nextBound := compute_preserves_candidate_bound current (inputs n) control.1 localBound
      change (step current (inputs n)).r5_nbReg = s.r5_nbReg ∧ _
      refine ⟨nextDivisor.trans divisor, ?_, 2 * q + bit, ?_, ?_⟩
      · simpa only [show current.r5_nbReg = s.r5_nbReg from divisor] using nextBound
      · rw [Nat.pow_succ]
        omega
      · change (step current (inputs n)).r2_nshiftReg.toNat + _ = _
        dsimp only at nextBalance
        rw [show current.r5_nbReg = s.r5_nbReg from divisor] at nextBalance
        simpa only [bit, show current.r5_nbReg = s.r5_nbReg from divisor, Nat.pow_succ, Nat.mul_right_comm (2^n) 2 s.r2_nshiftReg.toNat,
          Nat.mul_comm (2^n * s.r2_nshiftReg.toNat) 2] using nextBalance
private theorem decode_balance (z a d q : Nat)
    (qbound : q < 18446744073709551616)
    (bound : z / 18446744073709551616 < 2 * d)
    (balance : z + 36893488147419103232 * (q * d) =
      36893488147419103232 * a + q) :
    z % 18446744073709551616 = a / d ∧
      z / 36893488147419103232 = a % d := by
  have positive : 0 < d := by omega
  have identity : a = q * d + z / 36893488147419103232 := by omega
  have rbound : z / 36893488147419103232 < d := by omega
  have qvalue : z % 18446744073709551616 = q := by omega
  have result := RestoringDivision.quotient_remainder
    ⟨q, z / 36893488147419103232⟩ a d positive identity rbound
  exact ⟨qvalue.trans result.1, result.2⟩

theorem candidate_eq_div (sh : BitVec 129) :
    candidate sh = sh.toNat / 18446744073709551616 := by
  have split := split_shift_toNat sh
  have low := (BitVec.extractLsb' 0 64 sh).isLt
  omega

theorem final_remainder_toNat (sh : BitVec 129) :
    (BitVec.extractLsb' 65 64 sh).toNat = sh.toNat / 36893488147419103232 := by
  rw [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  have size := sh.isLt
  omega

/-- Execution of the generated compute datapath yields the mathematical
    quotient and remainder. The initialization obligation is the alignment of
    the captured dividend with the skipped-bit count, not a result assumption. -/
theorem compute_result (n : Nat) (s : State) (inputs : Nat → Inputs) (a : Nat)
    (state : s.r0_nstate = 3) (remaining : s.r9_ncnt_5Fvalue.toNat + n ≤ 64)
    (reset : ∀ t, t < n → (inputs t).nreset = 0)
    (initialBound : candidate s.r2_nshiftReg < 2 * s.r5_nbReg.toNat)
    (alignment : 2^n * s.r2_nshiftReg.toNat = 36893488147419103232 * a) :
    let final := run s inputs n
    (BitVec.extractLsb' 0 64 final.r2_nshiftReg).toNat = a / s.r5_nbReg.toNat ∧
    (BitVec.extractLsb' 65 64 final.r2_nshiftReg).toNat = a % s.r5_nbReg.toNat := by
  rcases compute_execution n s inputs state remaining reset initialBound with
    ⟨divisor, bound, q, qsize, balance⟩
  have size : 2^n ≤ 18446744073709551616 := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) (show n ≤ 64 by omega)
    exact h
  rw [alignment, Nat.mul_assoc, Nat.mul_comm s.r5_nbReg.toNat q] at balance
  rw [candidate_eq_div] at bound
  have decoded := decode_balance _ _ _ q (by omega) bound balance
  constructor
  · simpa only [BitVec.extractLsb'_toNat, Nat.shiftRight_zero] using decoded.1
  · rw [final_remainder_toNat]
    exact decoded.2
def metadata (s : State) : BitVec 1 × BitVec 1 × BitVec 1 × BitVec 1 :=
  (s.r3_naSignReg, s.r4_nqSignReg, s.r7_nctrlReg_5FisW, s.r8_nctrlReg_5FisHi)

theorem compute_metadata (s : State) (i : Inputs) (state : s.r0_nstate = 3) :
    metadata (step s i) = metadata s := by
  simp [metadata, step, eval, state]

theorem compute_execution_metadata (n : Nat) (s : State) (inputs : Nat → Inputs)
    (state : s.r0_nstate = 3) (remaining : s.r9_ncnt_5Fvalue.toNat + n ≤ 64)
    (reset : ∀ t, t < n → (inputs t).nreset = 0) :
    metadata (run s inputs n) = metadata s := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have control := compute_prefix n s inputs state (by omega)
        (by intro t ht; apply reset; omega)
      change metadata (step (run s inputs n) (inputs n)) = _
      rw [compute_metadata _ _ control.1]
      exact ih (by omega) (by intro t ht; apply reset; omega)
end nRadix2Divider
