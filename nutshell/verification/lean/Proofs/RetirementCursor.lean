import Proofs.RetirementPCOrder
namespace NutShellProofs
open nNutCore

noncomputable def RetirementCursor (s : State) : BitVec 39 :=
  (RetirementPCs s).headD s.g33.r1065_nfrontend_5Fifu_5Fpc

theorem pc_sequence_head (start next : BitVec 39) (pcs : List (BitVec 39))
    (chain : PCSequence start pcs next) : pcs.headD next = start := by
  cases pcs with
  | nil => exact chain.symm
  | cons pc rest => exact chain.1

theorem retirement_cursor_committed (s : State) (i : Inputs) (commit : v9 s i = 1) :
    RetirementCursor s = (WBUPair s).2 := by
  change s.g48.r1567_nbackend_5Fvalid_5F1 = 1 at commit
  simp [RetirementCursor, RetirementPCs, commit]

theorem retirement_cursor_remaining (s : State) (i : Inputs)
    (sequential : SequentialPCs (RetirementPCs s) s.g33.r1065_nfrontend_5Fifu_5Fpc) :
    PCSequence (if v9 s i = 1 then RetirementCursor s + 4 else RetirementCursor s)
      (IssuedPCs s) s.g33.r1065_nfrontend_5Fifu_5Fpc := by
  obtain ⟨start, chain⟩ := sequential
  have cursor : RetirementCursor s = start := pc_sequence_head _ _ _ chain
  rw [cursor]
  rcases BitVec.eq_zero_or_eq_one s.g48.r1567_nbackend_5Fvalid_5F1 with zero | one
  · simpa [RetirementPCs, zero, v9] using chain
  · have tail : PCSequence (start + 4) (IssuedPCs s) s.g33.r1065_nfrontend_5Fifu_5Fpc := by
      simp only [RetirementPCs, one] at chain
      exact chain.2
    simpa [v9, one] using tail

#print axioms retirement_cursor_remaining

theorem temporary_pc32_retirement_cursor_step (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (currentReset : (inputs (t + 1)).g0.nreset = 0)
    (noRedirect : v14 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    RetirementCursor (run initial inputs (t + 2)) =
      if v9 (run initial inputs (t + 1)) (inputs (t + 1)) = 1
      then RetirementCursor (run initial inputs (t + 1)) + 4
      else RetirementCursor (run initial inputs (t + 1)) := by
  have remaining := retirement_cursor_remaining (run initial inputs (t + 1)) (inputs (t + 1))
    (temporary_pc32_retirement_pcs_sequential initial inputs reset environment restriction t)
  have transition := retirement_pcs_step (run initial inputs (t + 1)) (inputs (t + 1))
    currentReset noRedirect (queue_occupancy_bound_run initial inputs reset t)
    (temporary_pc32_dequeue_eq_capture_run initial inputs reset environment restriction t currentReset noRedirect)
    (temporary_pc32_idu_capture_front initial inputs reset environment restriction t currentReset noRedirect)
    (fetch_not_delivered_run initial inputs reset t)
  change RetirementPCs (run initial inputs (t + 2)) = _ at transition
  unfold RetirementCursor at ⊢
  rw [transition, temporary_pc32_fetch_pc_transition initial inputs reset environment restriction t]
  rcases BitVec.eq_zero_or_eq_one (v25943 (run initial inputs (t + 1)) (inputs (t + 1))) with noCapture | capture
  · simpa [currentReset, noRedirect, noCapture, RetirementCursor] using pc_sequence_head _ _ _ remaining
  · simpa [currentReset, noRedirect, capture, RetirementCursor] using
      pc_sequence_head _ _ _ (pc_sequence_append_next _ _ _ remaining)

theorem retirement_cursor_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    RetirementCursor (step s i) = 0x80000000 := by
  rw [RetirementCursor, retirement_pcs_reset s i reset, List.headD_nil, fetch_pc_transition]
  simp [reset]

theorem retirement_cursor_redirect (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (redirect : v14 s i = 1) :
    RetirementCursor (step s i) = v2709 s i := by
  rw [RetirementCursor, retirement_pcs_flush s i redirect, List.headD_nil, fetch_pc_transition]
  simp [reset, redirect]

#print axioms temporary_pc32_retirement_cursor_step
#print axioms retirement_cursor_redirect
end NutShellProofs
