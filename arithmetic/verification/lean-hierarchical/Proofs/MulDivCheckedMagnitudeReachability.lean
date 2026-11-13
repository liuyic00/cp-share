import Proofs.MulDivCheckedMagnitudeRequest
import Proofs.MulDivCheckedMagnitudeTrace

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

theorem pending_response_magnitudes (s : State) (resetInput : Inputs) (inputs : Nat → Inputs)
    (reset : resetInput.nreset = 1) (n : Nat)
    (pending : (run (step s resetInput) inputs n).r9_ncontractPending = 1)
    (ready : v38 (run (step s resetInput) inputs n) (inputs n) = 1)
    (division : divisionRequest (recordedRequest (run (step s resetInput) inputs n))) :
    let current := run (step s resetInput) inputs n
    let request := recordedRequest current
    v232 current (inputs n) = magnitudeQuotient (divisionMagnitudeA request) (divisionMagnitudeB request) ∧
    v233 current (inputs n) = magnitudeResidue (divisionMagnitudeA request) (divisionMagnitudeB request) := by
  obtain ⟨k, before, idle, valid, legal, initialReset, initialKill, record, uninterrupted⟩ :=
    pending_origin s resetInput inputs reset n pending
  let initial := step s resetInput
  let extended := holdAfter inputs n
  have samePrefix (t : Nat) (h : t ≤ n) : run initial extended t = run initial inputs t :=
    hold_after_prefix initial inputs n t h
  have request : extended k = inputs k := by simp [extended, holdAfter, before]
  have noReset : ∀ t, t < 68 → (extended (k + t)).nreset = 0 := by
    intro t bound
    by_cases inside : k + t < n
    · have h : (inputs (k + t)).nreset = 0 := by
        by_cases zero : t = 0
        · simpa [zero] using initialReset
        · exact (uninterrupted (k + t) (by omega) inside).1
      simpa [extended, holdAfter, inside] using h
    · simp [extended, holdAfter, inside, holdInput]
  have noKill : ∀ t, t < 68 → (extended (k + t)).nio_5Fkill = 0 := by
    intro t bound
    by_cases inside : k + t < n
    · have h : (inputs (k + t)).nio_5Fkill = 0 := by
        by_cases zero : t = 0
        · simpa [zero] using initialKill
        · exact (uninterrupted (k + t) (by omega) inside).2.1
      simpa [extended, holdAfter, inside] using h
    · simp [extended, holdAfter, inside, holdInput]
  have operation : divisionRequest (inputs k) := by
    rw [record] at division
    exact division
  obtain ⟨m, lower, upper, response, quotient, residue⟩ := division_monitor_accepted
    (run initial extended k) (fun t => extended (k + t))
    (by rw [samePrefix k (by omega)]; exact idle)
    (by simpa [request] using valid) (by simpa [request] using operation) noReset noKill
  rw [← run_offset] at response quotient residue
  change v232 (run initial extended (k + m)) (extended (k + m)) =
    magnitudeQuotient (divisionMagnitudeA (extended k)) (divisionMagnitudeB (extended k)) at quotient
  change v233 (run initial extended (k + m)) (extended (k + m)) =
    magnitudeResidue (divisionMagnitudeA (extended k)) (divisionMagnitudeB (extended k)) at residue
  rw [request] at quotient residue
  have same : v232 (run initial inputs n) (inputs n) =
      v232 (run initial extended (k + m)) (extended (k + m)) ∧
      v233 (run initial inputs n) (inputs n) =
      v233 (run initial extended (k + m)) (extended (k + m)) := by
    by_cases earlier : k + m ≤ n
    · have extPending : (run initial extended n).r9_ncontractPending = 1 := by
        rw [samePrefix n (by omega)]; exact pending
      have noCapture : ∀ t, k + m ≤ t → t < n → v2 (run initial extended t) (extended t) ≠ 1 := by
        intro t lo hi
        rw [samePrefix t (by omega)]
        simpa [extended, holdAfter, hi] using (uninterrupted t (by omega) hi).2.2
      have stable := pending_magnitudes_stable initial extended (k + m) n extPending
        noCapture response n earlier (by omega)
      rw [samePrefix n (by omega)] at stable
      exact stable
    · have index : k + m = n + (k + m - n) := by omega
      have stable := hold_after_magnitudes initial inputs n (k + m - n) pending ready
      rw [← index] at stable
      exact ⟨stable.1.symm, stable.2.symm⟩
  dsimp only
  rw [record]
  exact ⟨same.1.trans quotient, same.2.trans residue⟩

#print axioms pending_response_magnitudes
end HierarchicalMulDivChecked
