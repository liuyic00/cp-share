import Proofs.MulDivCheckedNormalizedMagnitude
import Proofs.MulDivSignedRequest

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

theorem signed_setup_unsaved (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 4#4 ∨
      (inputs 0).nio_5Freq_5Fbits_5Ffn = 6#4)
    (reset : (inputs 0).nreset = 0) :
    (run s inputs (HierarchicalMulDiv.signedSetupTime (coreInputs (inputs 0)))).r16_ncontractWasNegated = 0 := by
  have captured : v2 s (inputs 0) = 1 := by simp [v2, v1, v0, idle, valid]
  have clear := snapshot_clear_on_capture s (inputs 0) captured
  have control := (HierarchicalMulDiv.capture_signed (coreState s) (coreInputs (inputs 0))
    idle valid reset operation).1
  rw [← core_step] at control
  have notCorrecting : (step s (inputs 0)).r0_nstate ≠ 5 := by
    change (step s (inputs 0)).r0_nstate = _ at control
    rw [control]
    split <;> decide
  unfold HierarchicalMulDiv.signedSetupTime
  split
  · exact unsaved_before_correction (step s (inputs 0)) (inputs 1) clear notCorrecting
  · exact clear

/-- Every accepted signed divide/remainder request produces correct monitor
    magnitudes, including word operands, zero divisors and signed overflow. -/
theorem signed_monitor_accepted (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 4#4 ∨
      (inputs 0).nio_5Freq_5Fbits_5Ffn = 6#4)
    (reset : ∀ t, t < 68 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 68 → (inputs t).nio_5Fkill = 0) :
    let request := coreInputs (inputs 0)
    let a := HierarchicalMulDiv.absoluteWord (HierarchicalMulDiv.signedA request)
    let d := HierarchicalMulDiv.absoluteWord (HierarchicalMulDiv.signedB request)
    ∃ n, 66 ≤ n ∧ n ≤ 68 ∧
      v38 (run s inputs n) (inputs n) = 1 ∧
      v232 (run s inputs n) (inputs n) = magnitudeQuotient a d ∧
      v233 (run s inputs n) (inputs n) = magnitudeResidue a d := by
  let start := HierarchicalMulDiv.signedSetupTime (coreInputs (inputs 0))
  have time := HierarchicalMulDiv.signed_setup_time (coreInputs (inputs 0))
  have prepared := HierarchicalMulDiv.signed_setup_run (coreState s)
    (fun t => coreInputs (inputs t)) idle valid operation
    (by intro t h; exact reset t (by omega)) (alive 1 (by omega))
  rw [← core_run s inputs start] at prepared
  have clear := signed_setup_unsaved s inputs idle valid operation (reset 0 (by omega))
  obtain ⟨n, elapsed, ready, quotient, residue⟩ := normalized_monitor_result
    (run s inputs start) (fun t => inputs (start + t)) _ _
    prepared.1 prepared.2.1 prepared.2.2.1 prepared.2.2.2.1 clear
    (by intro t h; apply reset; dsimp [start]; omega)
    (by intro t h; apply alive; dsimp [start]; omega)
  refine ⟨start + n, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [start]; omega
  · dsimp [start]; omega
  · rw [run_offset]; exact ready
  · rw [run_offset]; exact quotient
  · rw [run_offset]; exact residue

#print axioms signed_monitor_accepted
end HierarchicalMulDivChecked
