import Proofs.FrontendAlignedState
namespace NutShellProofs
open nNutCore

/-- Conditional invariant: valid fetch-head PC alignment is still outstanding. -/
theorem frontend_aligned_state_run_of_head (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (headAligned : ∀ k, v9802 (run initial inputs (k + 1)) (inputs (k + 1)) = 1 →
      BitVec.extractLsb' 0 2 (v9733 (run initial inputs (k + 1)) (inputs (k + 1))) = 0)
    (t : Nat) : FrontendAlignedState (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact frontend_aligned_state_reset _ _ reset
  | succ t ih => exact frontend_aligned_state_step_valid_head _ _ ih (environment (t + 1)) (headAligned t)

/-- Original frontend assertion, reduced to valid fetch-head alignment rather
than any requirement on uninitialized or invalid queue data. -/
theorem frontend_task0_run_of_head (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (headAligned : ∀ k, v9802 (run initial inputs (k + 1)) (inputs (k + 1)) = 1 →
      BitVec.extractLsb' 0 2 (v9733 (run initial inputs (k + 1)) (inputs (k + 1))) = 0)
    (t : Nat) : TaskHolds 0 (run initial inputs t) (inputs t) := by
  cases t with
  | zero => exact (asserts_iff_tasks _ _).mp (assertions_during_reset _ _ reset) 0
  | succ t =>
    have old := frontend_aligned_state_run_of_head initial inputs reset environment headAligned t
    rcases BitVec.eq_zero_or_eq_one (v9802 (run initial inputs (t + 1)) (inputs (t + 1))) with empty | valid
    · exact frontend_task0_of_empty _ _ empty
    · exact frontend_task0_of_offset_aligned _ _
        (frontend_selected_offset_aligned _ _ (headAligned t valid) old.2)
#print axioms frontend_aligned_state_run_of_head
#print axioms frontend_task0_run_of_head
end NutShellProofs
