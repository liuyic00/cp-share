import Proofs.RadixFinishInvariant
import Proofs.RadixZero

namespace nRadix2Divider
set_option maxRecDepth 8192

theorem zero_segment_correct (s : State) (inputs : Nat → Inputs)
    (state : s.r0_nstate = 3) (count : s.r9_ncnt_5Fvalue = 0)
    (flag : s.r1_ndivBy0Reg = 1) (zero : s.r5_nbReg = 0)
    (initial : s.r2_nshiftReg = 0#64 ++ s.r6_naValx2Reg)
    (reset : ∀ t, t < 64 → (inputs t).nreset = 0) :
    MagnitudeCorrect (run s inputs 64) := by
  have countNat : s.r9_ncnt_5Fvalue.toNat = 0 := congrArg BitVec.toNat count
  have result := compute_zero_run 64 s inputs state (by omega) reset zero
  have captured := compute_captured_run 64 s inputs state (by omega) reset
  unfold MagnitudeCorrect
  rw [captured.2.2, flag, if_pos rfl, result.2, initial, zeroRun_full, captured.2.1]
  bv_decide

theorem setup_captured (s : State) (log shift : Inputs) (state : s.r0_nstate = 1)
    (r0 : log.nreset = 0) (r1 : shift.nreset = 0) :
    (step (step s log) shift).r5_nbReg = s.r5_nbReg ∧
    (step (step s log) shift).r6_naValx2Reg = s.r6_naValx2Reg ∧
    (step (step s log) shift).r1_ndivBy0Reg = s.r1_ndivBy0Reg := by
  simp only [step, eval, state, r0, r1]
  bv_decide

/-- Both setup paths establish correct captured magnitudes at the exact finish
edge. The only capture requirements are the doubled dividend and zero flag. -/
theorem setup_segment_correct (s : State) (log shift : Inputs) (inputs : Nat → Inputs)
    (state : s.r0_nstate = 1) (r0 : log.nreset = 0) (r1 : shift.nreset = 0)
    (flag : (s.r1_ndivBy0Reg = 1 ↔ s.r5_nbReg = 0))
    (doubled : s.r6_naValx2Reg.toNat = 2 * (s.r6_naValx2Reg.extractLsb' 1 64).toNat)
    (reset : ∀ t, t < 64 - (step (step s log) shift).r9_ncnt_5Fvalue.toNat → (inputs t).nreset = 0) :
    let initialized := step (step s log) shift
    let n := 64 - initialized.r9_ncnt_5Fvalue.toNat
    (run initialized inputs n).r0_nstate = 4 ∧ MagnitudeCorrect (run initialized inputs n) := by
  let initialized := step (step s log) shift
  let n := 64 - initialized.r9_ncnt_5Fvalue.toNat
  have control : initialized.r0_nstate = 3 := shift_state _ _ (log2_state s log state r0) r1
  have captured := setup_captured s log shift state r0 r1
  have size := initialized.r9_ncnt_5Fvalue.isLt
  by_cases zero : s.r5_nbReg = 0
  · have zeroFlag := flag.mpr zero
    have setup := zero_setup s log shift state zeroFlag r0 r1
    have count : initialized.r9_ncnt_5Fvalue = 0 := setup.1
    have countNat : initialized.r9_ncnt_5Fvalue.toNat = 0 := congrArg BitVec.toNat count
    have length : n = 64 := by dsimp [n]; omega
    change (run initialized inputs n).r0_nstate = 4 ∧ MagnitudeCorrect (run initialized inputs n)
    have reset64 : ∀ t, t < 64 → (inputs t).nreset = 0 := by
      simpa only [show 64 - (step (step s log) shift).r9_ncnt_5Fvalue.toNat = 64 from length] using reset
    rw [length]
    refine ⟨compute_finishes 64 initialized inputs control (by omega) reset64, ?_⟩
    apply zero_segment_correct initialized inputs control count (captured.2.2.trans zeroFlag)
      (captured.1.trans zero) _ reset64
    rw [captured.2.1]
    exact setup.2
  · have zeroFlag : s.r1_ndivBy0Reg = 0 := by
      have notOne : s.r1_ndivBy0Reg ≠ 1 := fun h => zero (flag.mp h)
      bv_decide
    have result := setup_computes s log shift inputs (s.r6_naValx2Reg.extractLsb' 1 64).toNat
      state r0 r1 zero zeroFlag doubled reset
    have stable := compute_captured_run n initialized inputs control (by dsimp [n]; omega)
      (fun t h => reset t h)
    change (run initialized inputs n).r0_nstate = 4 ∧ MagnitudeCorrect (run initialized inputs n)
    refine ⟨result.1, ?_⟩
    unfold MagnitudeCorrect
    rw [stable.2.2, captured.2.2, zeroFlag, if_neg (by decide), stable.1, stable.2.1,
      captured.1, captured.2.1]
    have positive : s.r5_nbReg.toNat > 0 := by
      have ne : s.r5_nbReg.toNat ≠ 0 := by intro h; apply zero; exact BitVec.eq_of_toNat_eq h
      omega
    exact ⟨positive, result.2.1, result.2.2⟩

theorem capture_invariant (s : State) (i : Inputs)
    (idle : s.r0_nstate = 0) (valid : i.nio_5Fin_5Fvalid = 1) (reset : i.nreset = 0) :
    ((step s i).r1_ndivBy0Reg = 1 ↔ (step s i).r5_nbReg = 0) ∧
    (step s i).r6_naValx2Reg.toNat =
      2 * ((step s i).r6_naValx2Reg.extractLsb' 1 64).toNat := by
  constructor
  · simp only [step, eval, idle, valid, reset]
    bv_decide
  · have captured := (capture_magnitudes s i idle valid reset).1
    rw [captured]
    have slice (a : BitVec 64) : (a ++ 0#1).extractLsb' 1 64 = a := by bv_decide
    rw [slice, BitVec.toNat_append]
    simp [Nat.shiftLeft_eq, Nat.mul_comm]

/-- Every accepted request reaches a finish state satisfying the magnitude
invariant, including zero divisors and signed minimum operands. -/
theorem accepted_finish_invariant (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Fin_5Fvalid = 1)
    (reset : ∀ t, t < 67 → (inputs t).nreset = 0) :
    ∃ n, 4 ≤ n ∧ n ≤ 67 ∧ (run s inputs n).r0_nstate = 4 ∧ MagnitudeCorrect (run s inputs n) := by
  let captured := step s (inputs 0)
  let initialized := step (step captured (inputs 1)) (inputs 2)
  let n := 64 - initialized.r9_ncnt_5Fvalue.toNat
  have state : captured.r0_nstate = 1 := accept_state s _ idle (reset 0 (by decide)) valid
  have invariant := capture_invariant s (inputs 0) idle valid (reset 0 (by decide))
  have result := setup_segment_correct captured (inputs 1) (inputs 2) (fun t => inputs (t + 3))
    state (reset 1 (by decide)) (reset 2 (by decide)) invariant.1 invariant.2
    (fun t h => reset (t + 3) (by omega))
  have size := initialized.r9_ncnt_5Fvalue.isLt
  have length : 1 ≤ n ∧ n ≤ 64 := by dsimp [n]; omega
  have trace : run s inputs (n + 3) = run initialized (fun t => inputs (t + 3)) n := by
    rw [show n + 3 = (n + 2) + 1 by omega, run_from_next,
      show n + 2 = (n + 1) + 1 by omega, run_from_next, run_from_next]
  refine ⟨n + 3, by omega, by omega, ?_⟩
  rw [trace]
  exact result

theorem accepted_assertions (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Fin_5Fvalid = 1)
    (reset : ∀ t, t < 67 → (inputs t).nreset = 0) :
    ∃ n, 4 ≤ n ∧ n ≤ 67 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fout_5Fvalid = 1 ∧
      asserts (run s inputs n) (inputs n) := by
  rcases accepted_finish_invariant s inputs idle valid reset with ⟨n, lower, upper, finish, correct⟩
  refine ⟨n, lower, upper, finish_valid _ _ finish, ?_⟩
  cases n with
  | zero => omega
  | succ n =>
    exact finish_invariant_asserts (run s inputs n) (inputs n) (inputs (n + 1)) (fun _ => correct)

end nRadix2Divider
