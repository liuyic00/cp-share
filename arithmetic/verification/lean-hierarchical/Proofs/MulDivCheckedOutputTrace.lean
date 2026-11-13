import Proofs.MulDivCheckedHoldTrace

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

theorem pending_response_arithmetic (s : State) (resetInput : Inputs) (inputs : Nat → Inputs)
    (reset : resetInput.nreset = 1) (n : Nat)
    (pending : (run (step s resetInput) inputs n).r9_ncontractPending = 1)
    (ready : v38 (run (step s resetInput) inputs n) (inputs n) = 1) :
    (observe (run (step s resetInput) inputs n) (inputs n)).nio_5Fresp_5Fbits_5Fdata =
      arithmeticSpecification (recordedRequest (run (step s resetInput) inputs n)) := by
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
  have accepted := arithmetic_accepted (run initial extended k) (fun t => extended (k + t))
    (by rw [samePrefix k (by omega)]; exact idle)
    (by simpa [request] using valid) (by simpa [request] using legal) noReset noKill
  obtain ⟨m, lower, upper, response, tag, data⟩ := accepted
  rw [← run_offset] at response data
  change (observe (run initial extended (k + m)) (extended (k + m))).nio_5Fresp_5Fvalid = 1 at response
  change (observe (run initial extended (k + m)) (extended (k + m))).nio_5Fresp_5Fbits_5Fdata =
    arithmeticSpecification (extended k) at data
  rw [request] at data
  have sameData : (observe (run initial inputs n) (inputs n)).nio_5Fresp_5Fbits_5Fdata =
      (observe (run initial extended (k + m)) (extended (k + m))).nio_5Fresp_5Fbits_5Fdata := by
    by_cases earlier : k + m ≤ n
    · have extPending : (run initial extended n).r9_ncontractPending = 1 := by rw [samePrefix n (by omega)]; exact pending
      have noCapture : ∀ t, k + m ≤ t → t < n → v2 (run initial extended t) (extended t) ≠ 1 := by
        intro t lo hi
        rw [samePrefix t (by omega)]
        simpa [extended, holdAfter, hi] using (uninterrupted t (by omega) hi).2.2
      have stable := pending_data_stable initial extended (k + m) n extPending noCapture response earlier
      rw [samePrefix n (by omega)] at stable
      rw [core_output_input_independent (run initial inputs n) (inputs n) (extended n)]
      exact stable
    · have index : k + m = n + (k + m - n) := by omega
      have stable := hold_after_stable initial inputs n (k + m - n) pending ready
      rw [← index] at stable
      exact (congrArg (fun output => output.nio_5Fresp_5Fbits_5Fdata)
        (outputs_of_core_eq _ _ (extended (k + m)) (inputs n) stable)).symm
  rw [record]
  exact sameData.trans data

end HierarchicalMulDivChecked
