import Proofs.MulDivCheckedNormalizedMagnitude

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

theorem unsigned_monitor_accepted (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 5#4 ∨
      (inputs 0).nio_5Freq_5Fbits_5Ffn = 7#4)
    (reset : ∀ t, t < 68 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 68 → (inputs t).nio_5Fkill = 0) :
    let request := inputs 0
    let a := HierarchicalMulDiv.unsignedOperand request.nio_5Freq_5Fbits_5Fin1 request.nio_5Freq_5Fbits_5Fdw
    let d := HierarchicalMulDiv.unsignedOperand request.nio_5Freq_5Fbits_5Fin2 request.nio_5Freq_5Fbits_5Fdw
    ∃ n, 66 ≤ n ∧ n ≤ 68 ∧
      v38 (run s inputs n) (inputs n) = 1 ∧
      v232 (run s inputs n) (inputs n) = magnitudeQuotient a d ∧
      v233 (run s inputs n) (inputs n) = magnitudeResidue a d := by
  have prepared := HierarchicalMulDiv.capture_unsigned (coreState s) (coreInputs (inputs 0))
    idle valid (reset 0 (by omega)) operation
  rw [← core_step] at prepared
  have captured : v2 s (inputs 0) = 1 := by simp [v2, v1, v0, idle, valid]
  have clear := snapshot_clear_on_capture s (inputs 0) captured
  obtain ⟨n, time, ready, quotient, residue⟩ := normalized_monitor_result
    (step s (inputs 0)) (fun t => inputs (1 + t)) _ _
    prepared.1 prepared.2.1 prepared.2.2.1 prepared.2.2.2.1 clear
    (by intro t h; exact reset (1 + t) (by omega))
    (by intro t h; exact alive (1 + t) (by omega))
  refine ⟨1 + n, by omega, by omega, ?_, ?_, ?_⟩
  · rw [run_offset]; exact ready
  · rw [run_offset]; exact quotient
  · rw [run_offset]; exact residue

#print axioms unsigned_monitor_accepted
end HierarchicalMulDivChecked
