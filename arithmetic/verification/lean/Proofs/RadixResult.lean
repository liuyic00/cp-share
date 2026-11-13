import Proofs.RadixExecution

namespace nRadix2Divider
set_option maxRecDepth 4096

theorem shift_datapath (s : State) (i : Inputs) (state : s.r0_nstate = 2) :
    (step s i).r2_nshiftReg =
      (0#1 ++ ((0#63 ++ s.r6_naValx2Reg) <<< (0#122 ++ s.r9_ncnt_5Fvalue).toNat)) := by
  simp [step, eval, state]

private theorem shift_fits (a : BitVec 65) (count : BitVec 6) :
    a.toNat * 2^count.toNat < 2^128 := by
  have c := count.isLt
  have power : 2^count.toNat ≤ 2^63 := Nat.pow_le_pow_right (by decide) (by omega)
  have first := Nat.mul_lt_mul_of_pos_right a.isLt
    (Nat.two_pow_pos count.toNat)
  have second := Nat.mul_le_mul_left (2^65) power
  exact Nat.lt_of_lt_of_le first second

theorem shift_toNat (s : State) (i : Inputs) (state : s.r0_nstate = 2) :
    (step s i).r2_nshiftReg.toNat =
      s.r6_naValx2Reg.toNat * 2^s.r9_ncnt_5Fvalue.toNat := by
  rw [shift_datapath s i state, BitVec.toNat_append, BitVec.toNat_shiftLeft]
  repeat rw [BitVec.toNat_append]
  simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.zero_mul, Nat.zero_or,
    Nat.shiftLeft_eq]
  exact Nat.mod_eq_of_lt (shift_fits _ _)

/-- Setup does not change the captured doubled dividend or divisor. The shift
    stage also preserves the skip counter used to determine remaining work. -/
theorem setup_preserves (s : State) (i j : Inputs) (state : s.r0_nstate = 1)
    (reset : i.nreset = 0) (nextReset : j.nreset = 0) :
    (step (step s i) j).r5_nbReg = s.r5_nbReg ∧
    (step s i).r6_naValx2Reg = s.r6_naValx2Reg ∧
    (step (step s i) j).r9_ncnt_5Fvalue = (step s i).r9_ncnt_5Fvalue := by
  simp [step, eval, state, reset, nextReset]

/-- Setup plus the exact number of compute iterations produces the integer
    quotient/remainder of the captured magnitude. -/
theorem setup_computes (s : State) (log shift : Inputs) (inputs : Nat → Inputs)
    (a : Nat) (state : s.r0_nstate = 1)
    (r0 : log.nreset = 0) (r1 : shift.nreset = 0)
    (nonzero : s.r5_nbReg ≠ 0) (flag : s.r1_ndivBy0Reg = 0)
    (captured : s.r6_naValx2Reg.toNat = 2 * a)
    (reset : ∀ t, t < 64 - (step (step s log) shift).r9_ncnt_5Fvalue.toNat → (inputs t).nreset = 0) :
    let initialized := step (step s log) shift
    let n := 64 - initialized.r9_ncnt_5Fvalue.toNat
    let final := run initialized inputs n
    final.r0_nstate = 4 ∧
    (BitVec.extractLsb' 0 64 final.r2_nshiftReg).toNat = a / s.r5_nbReg.toNat ∧
    (BitVec.extractLsb' 65 64 final.r2_nshiftReg).toNat = a % s.r5_nbReg.toNat := by
  let shifted := step s log
  let initialized := step shifted shift
  let n := 64 - initialized.r9_ncnt_5Fvalue.toNat
  have hs : shifted.r0_nstate = 2 := log2_state s log state r0
  have hi : initialized.r0_nstate = 3 := shift_state shifted shift hs r1
  have preserved := setup_preserves s log shift state r0 r1
  have countBound := initialized.r9_ncnt_5Fvalue.isLt
  have count : initialized.r9_ncnt_5Fvalue.toNat + n = 64 := by dsimp [n]; omega
  have noReset : ∀ t, t < n → (inputs t).nreset = 0 := by
    intro t ht
    apply reset
    dsimp [n] at ht
    omega
  have alignment : 2^n * initialized.r2_nshiftReg.toNat = 36893488147419103232 * a := by
    rw [shift_toNat shifted shift hs, preserved.2.1, captured]
    have counter : shifted.r9_ncnt_5Fvalue.toNat + n = 64 := by
      rw [← preserved.2.2]
      exact count
    calc
      2^n * (2 * a * 2^shifted.r9_ncnt_5Fvalue.toNat) =
          (2^shifted.r9_ncnt_5Fvalue.toNat * 2^n) * (2 * a) := by ac_rfl
      _ = 2^64 * (2 * a) := by rw [← Nat.pow_add, counter]
      _ = 36893488147419103232 * a := by rw [← Nat.mul_assoc]
  have bound : candidate initialized.r2_nshiftReg < 2 * initialized.r5_nbReg.toNat := by
    rw [preserved.1]
    exact skip_initializes_bound s log shift state r0 r1 nonzero flag
  have result := compute_result n initialized inputs a hi (by omega) noReset bound alignment
  change (run initialized inputs n).r0_nstate = 4 ∧ _
  refine ⟨compute_finishes n initialized inputs hi count noReset, ?_⟩
  have divisor : initialized.r5_nbReg = s.r5_nbReg := preserved.1
  simpa only [divisor] using result
def magnitude (x : BitVec 64) (signed : BitVec 1) : BitVec 64 :=
  if signed = 1 ∧ x.msb = true then -x else x

theorem capture_magnitudes (s : State) (i : Inputs)
    (idle : s.r0_nstate = 0) (valid : i.nio_5Fin_5Fvalid = 1) (reset : i.nreset = 0) :
    (step s i).r6_naValx2Reg = (magnitude i.nio_5Fin_5Fbits_5Fsrc_5F0 i.nctrl_5Fsign ++ 0#1) ∧
    (step s i).r5_nbReg = magnitude i.nio_5Fin_5Fbits_5Fsrc_5F1 i.nctrl_5Fsign := by
  simp only [step, eval, idle, valid, reset, magnitude]
  bv_decide

theorem setup_metadata (s : State) (i j : Inputs) (state : s.r0_nstate = 1)
    (r0 : i.nreset = 0) (r1 : j.nreset = 0) :
    metadata (step (step s i) j) = metadata s := by
  simp [metadata, step, eval, state, r0, r1]

/-- End-to-end magnitude division from a real accepted request: arbitrary
    later pins, no reset during the bound, and a nonzero divisor. -/
theorem accepted_magnitudes_correct (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Fin_5Fvalid = 1)
    (reset : ∀ t, t < 67 → (inputs t).nreset = 0)
    (nonzero : (inputs 0).nio_5Fin_5Fbits_5Fsrc_5F1 ≠ 0) :
    let a := magnitude (inputs 0).nio_5Fin_5Fbits_5Fsrc_5F0 (inputs 0).nctrl_5Fsign
    let b := magnitude (inputs 0).nio_5Fin_5Fbits_5Fsrc_5F1 (inputs 0).nctrl_5Fsign
    ∃ n, 4 ≤ n ∧ n ≤ 67 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fout_5Fvalid = 1 ∧
      (BitVec.extractLsb' 0 64 (run s inputs n).r2_nshiftReg).toNat = a.toNat / b.toNat ∧
      (BitVec.extractLsb' 65 64 (run s inputs n).r2_nshiftReg).toNat = a.toNat % b.toNat ∧
      metadata (run s inputs n) = metadata (step s (inputs 0)) := by
  let captured := step s (inputs 0)
  let initialized := step (step captured (inputs 1)) (inputs 2)
  let remaining := 64 - initialized.r9_ncnt_5Fvalue.toNat
  have r0 := reset 0 (by omega)
  have r1 := reset 1 (by omega)
  have r2 := reset 2 (by omega)
  have state : captured.r0_nstate = 1 := accept_state s _ idle r0 valid
  have mags := capture_magnitudes s (inputs 0) idle valid r0
  have divisor := accept_nonzero s (inputs 0) idle valid r0 nonzero
  have dividend : captured.r6_naValx2Reg.toNat =
      2 * (magnitude (inputs 0).nio_5Fin_5Fbits_5Fsrc_5F0 (inputs 0).nctrl_5Fsign).toNat := by
    change (step s (inputs 0)).r6_naValx2Reg.toNat = _
    rw [mags.1, BitVec.toNat_append]
    simp [Nat.shiftLeft_eq, Nat.mul_comm]
  have result := setup_computes captured (inputs 1) (inputs 2) (fun t => inputs (t + 3))
    _ state r1 r2 divisor.1 divisor.2 dividend (by intro t ht; apply reset; omega)
  have bound := initialized.r9_ncnt_5Fvalue.isLt
  have size : 1 ≤ remaining ∧ remaining ≤ 64 := by dsimp [remaining]; omega
  have trace : run s inputs (remaining + 3) =
      run initialized (fun t => inputs (t + 3)) remaining := by
    rw [show remaining + 3 = (remaining + 2) + 1 by omega, run_from_next,
      show remaining + 2 = (remaining + 1) + 1 by omega, run_from_next, run_from_next]
  refine ⟨remaining + 3, by omega, by omega, ?_, ?_⟩
  · rw [trace]
    exact finish_valid _ _ result.1
  · rw [trace]
    have b : captured.r5_nbReg =
        magnitude (inputs 0).nio_5Fin_5Fbits_5Fsrc_5F1 (inputs 0).nctrl_5Fsign := mags.2
    have numeric := result.2
    refine ⟨?_, ?_, ?_⟩
    · simpa only [b] using numeric.1
    · simpa only [b] using numeric.2
    · have hstate : initialized.r0_nstate = 3 :=
        shift_state _ _ (log2_state captured _ state r1) r2
      rw [compute_execution_metadata remaining initialized _ hstate
        (by dsimp [remaining]; omega) (by intro t ht; apply reset; dsimp [remaining] at ht; omega)]
      exact setup_metadata captured _ _ state r1 r2
end nRadix2Divider
