import Proofs.FrontendPageFaultRun
namespace NutShellProofs
open nNutCore

theorem csr_write_gate_zero (s : State) (i : Inputs)
    (inactive : v6 s i = 0 ∨ v3 s i ≠ 3 ∨ v28 s i = 0) :
    v13472 s i = 0 := by
  rcases inactive with idle | other | zero
  · simp [v13472, v13454, v13451, v13185, v13181, v13180, v13178, idle]
  · have unit : v13177 s i = 0 := by
      unfold v13177 v13176
      exact if_neg other
    simp [v13472, v13454, v13451, v13185, v13181, v13180, v13178, unit]
  · simp [v13472, v13454, v13451, v13185, v13184, v13182, v13183, zero]

theorem csr_mie_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    (step s i).g43.r1378_nbackend_5Fexu_5Fcsr_5Fmie = 0 := by
  change v13876 s i = 0
  simp [v13876, v13172, v12103, v11455, reset, v4051]

theorem csr_mie_zero_step (s : State) (i : Inputs)
    (old : s.g43.r1378_nbackend_5Fexu_5Fcsr_5Fmie = 0)
    (noWrite : v13472 s i = 0) :
    (step s i).g43.r1378_nbackend_5Fexu_5Fcsr_5Fmie = 0 := by
  change v13876 s i = 0
  simp [v13876, v13875, v13874, v13865, v13868, noWrite, old, v4051]

theorem csr_mie_zero_disables_interrupt (s : State) (i : Inputs)
    (mie : s.g43.r1378_nbackend_5Fexu_5Fcsr_5Fmie = 0) :
    v10039 s i = 0 := by
  simp [v10039, v10037, v10036, v10035, v10034, v10033, v10032,
    v10031, v9859, v9834, mie, v10038]
#print axioms csr_write_gate_zero
#print axioms csr_mie_zero_step
#print axioms csr_mie_zero_disables_interrupt
/-- Local coverage obligation remains explicit until instruction decode discharges it. -/
theorem csr_mie_zero_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (coverage : ∀ k, v6 (run initial inputs (k + 1)) (inputs (k + 1)) = 0 ∨
      v3 (run initial inputs (k + 1)) (inputs (k + 1)) ≠ 3 ∨
      v28 (run initial inputs (k + 1)) (inputs (k + 1)) = 0) (t : Nat) :
    (run initial inputs (t + 1)).g43.r1378_nbackend_5Fexu_5Fcsr_5Fmie = 0 := by
  induction t with
  | zero => exact csr_mie_reset initial (inputs 0) reset
  | succ t ih => exact csr_mie_zero_step _ _ ih (csr_write_gate_zero _ _ (coverage t))
#print axioms csr_mie_zero_run
end NutShellProofs
