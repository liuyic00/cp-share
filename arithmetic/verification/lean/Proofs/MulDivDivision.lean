import Proofs.MulDivControl
import Proofs.RadixExecution

namespace MulDivDivision
open nMulDiv
open nRadix2Divider (candidate lowCandidate restoringStep reducedWord quotientBit)

def packed (s : State) : BitVec 129 := s.r8_nremainder.extractLsb' 0 129

def difference (sh : BitVec 129) (d : BitVec 65) : BitVec 65 :=
  sh.extractLsb' 64 65 - d

def signBit (sh : BitVec 129) (d : BitVec 65) : BitVec 1 :=
  (difference sh d).extractLsb' 64 1

def divisionStep (sh : BitVec 129) (d : BitVec 65) : BitVec 129 :=
  let remainder := if signBit sh d = 1 then lowCandidate sh
    else (difference sh d).extractLsb' 0 64
  (remainder ++ sh.extractLsb' 0 64) ++ (signBit sh d ^^^ 1)

/-- Exact refinement of the exported Rocket division edge, including its
65-bit subtraction-sign implementation of the comparison. -/
theorem compute_datapath (s : State) (i : Inputs) (state : s.r0_nstate = 3) :
    (step s i).r8_nremainder = 0#1 ++ divisionStep (packed s) s.r7_ndivisor := by
  simp only [step, eval, state, divisionStep, signBit, difference, packed, lowCandidate]
  bv_decide

theorem divisor_stable (s : State) (i : Inputs) (state : s.r0_nstate = 3) :
    (step s i).r7_ndivisor = s.r7_ndivisor := by
  simp [step, eval, state]

/-- A subtraction sign is a valid unsigned comparison under the restoring
bound; no assumption that the candidate fits in 64 bits is needed. -/
theorem signBit_correct (sh : BitVec 129) (d : BitVec 64)
    (bound : candidate sh < 2 * d.toNat) :
    signBit sh (0#1 ++ d) = if d.toNat ≤ candidate sh then 0 else 1 := by
  have hd := d.isLt
  apply BitVec.eq_of_toNat_eq
  simp only [signBit, difference, BitVec.extractLsb'_toNat, BitVec.toNat_sub,
    nRadix2Divider.extend_toNat, Nat.shiftRight_eq_div_pow, Nat.reducePow]
  simp only [candidate, BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow, Nat.reducePow] at bound ⊢
  split <;> simp <;> omega

theorem step_refines_restoring (sh : BitVec 129) (d : BitVec 64)
    (bound : candidate sh < 2 * d.toNat) :
    divisionStep sh (0#1 ++ d) = restoringStep sh d := by
  have low : (difference sh (0#1 ++ d)).extractLsb' 0 64 = lowCandidate sh - d := by
    simp only [difference, lowCandidate]
    bv_decide
  by_cases choose : d.toNat ≤ candidate sh <;>
    simp [divisionStep, signBit_correct sh d bound, choose,
      restoringStep, reducedWord, quotientBit, low]

theorem packed_step (s : State) (i : Inputs) (d : BitVec 64)
    (state : s.r0_nstate = 3) (divisor : s.r7_ndivisor = 0#1 ++ d)
    (bound : candidate (packed s) < 2 * d.toNat) :
    packed (step s i) = restoringStep (packed s) d := by
  unfold packed at ⊢
  rw [compute_datapath s i state, divisor, step_refines_restoring _ d bound]
  change (0#1 ++ restoringStep (packed s) d).extractLsb' 0 129 = restoringStep (packed s) d
  generalize restoringStep (packed s) d = result
  bv_decide

/-- A proof-only state of the already verified restoring datapath. -/
def shadow (s : State) (d : BitVec 64) : nRadix2Divider.State := {
  r0_nstate := 3, r1_ndivBy0Reg := 0, r2_nshiftReg := packed s,
  r3_naSignReg := 0, r4_nqSignReg := 0, r5_nbReg := d,
  r6_naValx2Reg := 0, r7_nctrlReg_5FisW := 0, r8_nctrlReg_5FisHi := 0,
  r9_ncnt_5Fvalue := 0, r10_nhistoryValid := 0, r11_npreviousState := 0,
  r12_npreviousCount := 0, r13_nwasStalled := 0, r14_npreviousOutput := 0 }

def shadowInputs : nRadix2Divider.Inputs := by constructor <;> exact 0

theorem div_prefix (n : Nat) (s : State) (inputs : Nat → Inputs)
    (state : s.r0_nstate = 3) (remaining : s.r3_ncount.toNat + n < 65)
    (reset : ∀ t, t < n → (inputs t).nreset = 0)
    (kill : ∀ t, t < n → (inputs t).nio_5Fkill = 0) :
    (run s inputs n).r0_nstate = 3 ∧
    (run s inputs n).r3_ncount.toNat = s.r3_ncount.toNat + n := by
  induction n with
  | zero => simpa [run] using state
  | succ n ih =>
    have prior := ih (by omega) (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
    have edge := MulDivControl.div_edge (run s inputs n) (inputs n) prior.1
      (reset n (by omega)) (kill n (by omega))
    have notLast : (run s inputs n).r3_ncount ≠ 64 := by
      intro eq
      have : (run s inputs n).r3_ncount.toNat = 64 := congrArg BitVec.toNat eq
      omega
    constructor
    · change (step (run s inputs n) (inputs n)).r0_nstate = _
      simpa only [notLast, if_false] using edge.1
    · change (step (run s inputs n) (inputs n)).r3_ncount.toNat = _
      rw [edge.2, BitVec.toNat_add]
      change ((run s inputs n).r3_ncount.toNat + 1) % 128 = _
      omega

/-- Simulation relates all 64 remaining Rocket edges to the already verified
Radix2Divider core, without assuming the desired quotient or remainder. -/
theorem simulate (n : Nat) (s : State) (inputs : Nat → Inputs) (d : BitVec 64)
    (state : s.r0_nstate = 3) (count : s.r3_ncount = 1) (limit : n ≤ 64)
    (divisor : s.r7_ndivisor = 0#1 ++ d)
    (initialBound : candidate (packed s) < 2 * d.toNat)
    (reset : ∀ t, t < n → (inputs t).nreset = 0)
    (kill : ∀ t, t < n → (inputs t).nio_5Fkill = 0) :
    packed (run s inputs n) =
      (nRadix2Divider.run (shadow s d) (fun _ => shadowInputs) n).r2_nshiftReg ∧
    (run s inputs n).r7_ndivisor = 0#1 ++ d := by
  induction n with
  | zero => exact ⟨rfl, divisor⟩
  | succ n ih =>
    have prior := ih (by omega) (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
    have countNat : s.r3_ncount.toNat = 1 := congrArg BitVec.toNat count
    have rocket := div_prefix n s inputs state (by omega)
      (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
    have reference := nRadix2Divider.compute_prefix n (shadow s d) (fun _ => shadowInputs)
      rfl (by simp [shadow]; omega) (fun _ _ => rfl)
    have invariant := nRadix2Divider.compute_execution n (shadow s d) (fun _ => shadowInputs)
      rfl (by simp [shadow]; omega) (fun _ _ => rfl) initialBound
    have localBound : candidate (packed (run s inputs n)) < 2 * d.toNat := by
      rw [prior.1]
      exact invariant.2.1
    constructor
    · change packed (step (run s inputs n) (inputs n)) =
        (nRadix2Divider.step (nRadix2Divider.run (shadow s d) (fun _ => shadowInputs) n) shadowInputs).r2_nshiftReg
      rw [packed_step _ _ d rocket.1 prior.2 localBound,
        nRadix2Divider.compute_datapath _ _ reference.1, prior.1, invariant.1]
      rfl
    · change (step (run s inputs n) (inputs n)).r7_ndivisor = _
      rw [divisor_stable _ _ rocket.1, prior.2]

/-- Quotient and remainder in the actual Rocket registers after the 64
significant restoring iterations. The preceding leading iteration has doubled
the captured dividend; neither final result is assumed. -/
theorem magnitude_result (s : State) (inputs : Nat → Inputs) (a d : BitVec 64)
    (state : s.r0_nstate = 3) (count : s.r3_ncount = 1)
    (divisor : s.r7_ndivisor = 0#1 ++ d) (positive : 0 < d.toNat)
    (alignment : (packed s).toNat = 2 * a.toNat)
    (reset : ∀ t, t < 64 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 64 → (inputs t).nio_5Fkill = 0) :
    ((packed (run s inputs 64)).extractLsb' 0 64).toNat = a.toNat / d.toNat ∧
    ((packed (run s inputs 64)).extractLsb' 65 64).toNat = a.toNat % d.toNat := by
  have size := a.isLt
  have bound : candidate (packed s) < 2 * d.toNat := by
    rw [nRadix2Divider.candidate_eq_div, alignment]
    omega
  have simulation := simulate 64 s inputs d state count (by decide) divisor bound reset kill
  have result := nRadix2Divider.compute_result 64 (shadow s d) (fun _ => shadowInputs)
    a.toNat rfl (by change (0 : Nat) + 64 ≤ 64; decide) (fun _ _ => rfl) bound (by
      change 18446744073709551616 * (packed s).toNat = 36893488147419103232 * a.toNat
      rw [alignment]
      omega)
  rw [simulation.1]
  exact result

private theorem leading_candidate (a : BitVec 64) : candidate (0#65 ++ a) = 0 := by
  have high : (0#65 ++ a).extractLsb' 64 65 = 0#65 := by bv_decide
  unfold candidate
  rw [high]
  rfl

private theorem leading_step (a d : BitVec 64) (positive : 0 < d.toNat) :
    restoringStep (0#65 ++ a) d = (0#64 ++ a) ++ 0#1 := by
  have high := leading_candidate a
  have low : lowCandidate (0#65 ++ a) = 0 := by
    simp only [lowCandidate]
    bv_decide
  have data : (0#65 ++ a).extractLsb' 0 64 = a := by bv_decide
  have notSubtract : ¬ d.toNat ≤ candidate (0#65 ++ a) := by rw [high]; omega
  simp only [restoringStep, reducedWord, quotientBit, notSubtract, if_false, low, data]
  rfl

/-- Full 65-edge nonzero magnitude division, starting from the captured
dividend and divisor before the leading iteration. Sign restoration and output
formatting occur separately in the Rocket controller. -/
theorem full_magnitude_result (s : State) (inputs : Nat → Inputs) (a d : BitVec 64)
    (state : s.r0_nstate = 3) (count : s.r3_ncount = 0)
    (divisor : s.r7_ndivisor = 0#1 ++ d) (positive : 0 < d.toNat)
    (initial : packed s = 0#65 ++ a)
    (reset : ∀ t, t < 65 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 65 → (inputs t).nio_5Fkill = 0) :
    ((packed (run s inputs 65)).extractLsb' 0 64).toNat = a.toNat / d.toNat ∧
    ((packed (run s inputs 65)).extractLsb' 65 64).toNat = a.toNat % d.toNat := by
  have bound : candidate (packed s) < 2 * d.toNat := by
    rw [initial, leading_candidate]
    omega
  have edge := MulDivControl.div_edge s (inputs 0) state (reset 0 (by decide)) (kill 0 (by decide))
  have nextState : (step s (inputs 0)).r0_nstate = 3 := by simpa [count] using edge.1
  have nextCount : (step s (inputs 0)).r3_ncount = 1 := by simpa [count] using edge.2
  have nextDivisor : (step s (inputs 0)).r7_ndivisor = 0#1 ++ d := by
    rw [divisor_stable _ _ state, divisor]
  have alignment : (packed (step s (inputs 0))).toNat = 2 * a.toNat := by
    rw [packed_step _ _ d state divisor bound, initial, leading_step a d positive,
      nRadix2Divider.concatenate_step_toNat]
    simp
  have result := magnitude_result (step s (inputs 0)) (fun t => inputs (t + 1)) a d
    nextState nextCount nextDivisor positive alignment
    (fun t h => reset (t + 1) (by omega)) (fun t h => kill (t + 1) (by omega))
  rw [show 65 = 64 + 1 from rfl, MulDivControl.run_from_next]
  exact result

theorem unsigned_capture (s : State) (i : Inputs)
    (idle : s.r0_nstate = 0) (valid : i.nio_5Freq_5Fvalid = 1)
    (reset : i.nreset = 0) (full : i.nio_5Freq_5Fbits_5Fdw = 1)
    (operation : i.nio_5Freq_5Fbits_5Ffn = 5 ∨ i.nio_5Freq_5Fbits_5Ffn = 7) :
    (step s i).r0_nstate = 3 ∧ (step s i).r3_ncount = 0 ∧
    (step s i).r7_ndivisor = 0#1 ++ i.nio_5Freq_5Fbits_5Fin2 ∧
    packed (step s i) = 0#65 ++ i.nio_5Freq_5Fbits_5Fin1 := by
  rcases operation with operation | operation <;>
    simp only [step, eval, packed, idle, valid, reset, full, operation] <;> bv_decide

/-- For accepted 64-bit unsigned division/remainder requests, the actual
registers contain the mathematical quotient and remainder after 65 further
edges. This theorem precedes the separate output-formatting proof. -/
theorem unsigned_accepted_magnitudes (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (full : (inputs 0).nio_5Freq_5Fbits_5Fdw = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 5 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 7)
    (nonzero : (inputs 0).nio_5Freq_5Fbits_5Fin2 ≠ 0)
    (reset : ∀ t, t < 66 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 66 → (inputs t).nio_5Fkill = 0) :
    ((packed (run s inputs 66)).extractLsb' 0 64).toNat =
      (inputs 0).nio_5Freq_5Fbits_5Fin1.toNat / (inputs 0).nio_5Freq_5Fbits_5Fin2.toNat ∧
    ((packed (run s inputs 66)).extractLsb' 65 64).toNat =
      (inputs 0).nio_5Freq_5Fbits_5Fin1.toNat % (inputs 0).nio_5Freq_5Fbits_5Fin2.toNat := by
  have captured := unsigned_capture s (inputs 0) idle valid (reset 0 (by decide)) full operation
  have positive : 0 < (inputs 0).nio_5Freq_5Fbits_5Fin2.toNat := by
    have notZero : (inputs 0).nio_5Freq_5Fbits_5Fin2.toNat ≠ 0 := by
      intro h
      apply nonzero
      apply BitVec.eq_of_toNat_eq
      exact h
    omega
  have result := full_magnitude_result (step s (inputs 0)) (fun t => inputs (t + 1))
    (inputs 0).nio_5Freq_5Fbits_5Fin1 (inputs 0).nio_5Freq_5Fbits_5Fin2
    captured.1 captured.2.1 captured.2.2.1 positive captured.2.2.2
    (fun t h => reset (t + 1) (by omega)) (fun t h => kill (t + 1) (by omega))
  rw [show 66 = 65 + 1 from rfl, MulDivControl.run_from_next]
  exact result

end MulDivDivision
