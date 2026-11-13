import Proofs.RadixResult

namespace nRadix2Divider
set_option maxRecDepth 8192

def zeroStep (sh : BitVec 129) : BitVec 129 := (sh <<< 1) ||| 1

def zeroRun : Nat → BitVec 129 → BitVec 129
  | 0, sh => sh
  | n + 1, sh => zeroStep (zeroRun n sh)

theorem compute_zero_step (s : State) (i : Inputs)
    (state : s.r0_nstate = 3) (zero : s.r5_nbReg = 0) :
    (step s i).r2_nshiftReg = zeroStep s.r2_nshiftReg := by
  rw [compute_datapath s i state]
  simp [restoringStep, reducedWord, quotientBit, lowCandidate, zero, zeroStep]
  bv_decide

theorem zeroRun_full (a : BitVec 65) :
    zeroRun 64 (0#64 ++ a) = a ++ 18446744073709551615#64 := by
  simp only [zeroRun, zeroStep]
  bv_decide

theorem compute_zero_run (n : Nat) (s : State) (inputs : Nat → Inputs)
    (state : s.r0_nstate = 3) (remaining : s.r9_ncnt_5Fvalue.toNat + n ≤ 64)
    (reset : ∀ t, t < n → (inputs t).nreset = 0) (zero : s.r5_nbReg = 0) :
    (run s inputs n).r5_nbReg = 0 ∧
    (run s inputs n).r2_nshiftReg = zeroRun n s.r2_nshiftReg := by
  induction n with
  | zero => exact ⟨zero, rfl⟩
  | succ n ih =>
      have prior := ih (by omega) (by intro t ht; apply reset; omega)
      have control := compute_prefix n s inputs state (by omega)
        (by intro t ht; apply reset; omega)
      change (step (run s inputs n) (inputs n)).r5_nbReg = 0 ∧ _
      constructor
      · exact ((compute_preserves_captured _ _ control.1).1).trans prior.1
      · change (step (run s inputs n) (inputs n)).r2_nshiftReg = _
        rw [compute_zero_step _ _ control.1 prior.1, prior.2]
        rfl

theorem zero_setup (s : State) (i j : Inputs)
    (state : s.r0_nstate = 1) (flag : s.r1_ndivBy0Reg = 1)
    (r0 : i.nreset = 0) (r1 : j.nreset = 0) :
    (step (step s i) j).r9_ncnt_5Fvalue = 0 ∧
    (step (step s i) j).r2_nshiftReg = (0#64 ++ s.r6_naValx2Reg) := by
  simp only [step, eval, state, flag, r0, r1]
  bv_decide

theorem capture_zero (s : State) (i : Inputs)
    (idle : s.r0_nstate = 0) (valid : i.nio_5Fin_5Fvalid = 1)
    (reset : i.nreset = 0) (zero : i.nio_5Fin_5Fbits_5Fsrc_5F1 = 0) :
    (step s i).r5_nbReg = 0 ∧ (step s i).r1_ndivBy0Reg = 1 := by
  simp only [step, eval, idle, valid, reset, zero]
  bv_decide

/-- Divide by zero is complete after 66 further edges, with an all-ones
    magnitude quotient and the unchanged dividend magnitude as remainder. -/
theorem accepted_zero_magnitudes (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Fin_5Fvalid = 1)
    (reset : ∀ t, t < 67 → (inputs t).nreset = 0)
    (zero : (inputs 0).nio_5Fin_5Fbits_5Fsrc_5F1 = 0) :
    (observe (run s inputs 67) (inputs 67)).nio_5Fout_5Fvalid = 1 ∧
    (BitVec.extractLsb' 0 64 (run s inputs 67).r2_nshiftReg) = 18446744073709551615#64 ∧
    (BitVec.extractLsb' 65 64 (run s inputs 67).r2_nshiftReg) =
      magnitude (inputs 0).nio_5Fin_5Fbits_5Fsrc_5F0 (inputs 0).nctrl_5Fsign ∧
    metadata (run s inputs 67) = metadata (step s (inputs 0)) := by
  let captured := step s (inputs 0)
  let initialized := step (step captured (inputs 1)) (inputs 2)
  let later := fun t => inputs (t + 3)
  have r0 := reset 0 (by omega)
  have r1 := reset 1 (by omega)
  have r2 := reset 2 (by omega)
  have state : captured.r0_nstate = 1 := accept_state s _ idle r0 valid
  have data := capture_zero s (inputs 0) idle valid r0 zero
  have setup := zero_setup captured (inputs 1) (inputs 2) state data.2 r1 r2
  have hi : initialized.r0_nstate = 3 :=
    shift_state _ _ (log2_state captured _ state r1) r2
  have count : initialized.r9_ncnt_5Fvalue.toNat + 64 = 64 := by
    change (step (step captured (inputs 1)) (inputs 2)).r9_ncnt_5Fvalue.toNat + 64 = 64
    rw [setup.1]
    rfl
  have noReset : ∀ t, t < 64 → (later t).nreset = 0 := by
    intro t ht
    apply reset
    omega
  have divisor : initialized.r5_nbReg = 0 :=
    (setup_preserves captured _ _ state r1 r2).1.trans data.1
  have computed := compute_zero_run 64 initialized later hi (by omega) noReset divisor
  have finalData : (run initialized later 64).r2_nshiftReg =
      captured.r6_naValx2Reg ++ 18446744073709551615#64 := by
    rw [computed.2]
    change zeroRun 64 (step (step captured (inputs 1)) (inputs 2)).r2_nshiftReg = _
    rw [setup.2, zeroRun_full]
  have trace : run s inputs 67 = run initialized later 64 := by
    rw [show 67 = 66 + 1 by rfl, run_from_next,
      show 66 = 65 + 1 by rfl, run_from_next, run_from_next]
  rw [trace]
  refine ⟨finish_valid _ _ (compute_finishes 64 initialized later hi count noReset), ?_, ?_, ?_⟩
  · rw [finalData]
    bv_decide
  · rw [finalData]
    have magnitude := (capture_magnitudes s (inputs 0) idle valid r0).1
    change (step s (inputs 0)).r6_naValx2Reg = _ at magnitude
    rw [magnitude]
    bv_decide
  · rw [compute_execution_metadata 64 initialized later hi (by omega) noReset]
    exact setup_metadata captured _ _ state r1 r2
end nRadix2Divider
