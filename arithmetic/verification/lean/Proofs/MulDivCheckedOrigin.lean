import Proofs.MulDivCheckedControl

namespace MulDivCheckedOrigin
open nMulDivChecked

private theorem pending_edge (s : State) (i : Inputs) (pending : (step s i).r9_ncontractPending = 1) :
    i.nreset = 0 ∧ i.nio_5Fkill = 0 ∧
      ((s.r0_nstate = 0 ∧ i.nio_5Freq_5Fvalid = 1) ∨ s.r9_ncontractPending = 1) := by
  simp only [step, eval] at pending
  bv_decide

private theorem pending_not_acknowledged (s : State) (i : Inputs)
    (pending : (step s i).r9_ncontractPending = 1) :
    (observe s i).nio_5Fresp_5Fvalid = 0 ∨ i.nio_5Fresp_5Fready = 0 := by
  simp only [step, eval] at pending
  simp only [observe, eval]
  bv_decide

private theorem accepted_legal (s : State) (i : Inputs)
    (ready : s.r0_nstate = 0) (valid : i.nio_5Freq_5Fvalid = 1)
    (pending : (step s i).r9_ncontractPending = 1) : MulDivCheckedHistory.legal i := by
  simp only [step, eval, ready, valid] at pending
  change i.nio_5Freq_5Fbits_5Ffn < 8#4 ∧
    (i.nio_5Freq_5Fbits_5Fdw = 1 ∨ i.nio_5Freq_5Fbits_5Ffn = 0 ∨ 4#4 ≤ i.nio_5Freq_5Fbits_5Ffn)
  bv_decide

/-- Every outstanding monitor after reset belongs to an actual legal accepted
request. Its captured operands still equal that request, and no reset or kill
or response acknowledgement has occurred between acceptance and the current observation. -/
theorem pending_origin (initial : State) (resetInput : Inputs) (reset : resetInput.nreset = 1)
    (pins : Nat → Inputs) (n : Nat)
    (pending : (run (step initial resetInput) pins n).r9_ncontractPending = 1) :
    ∃ k, k < n ∧ (run (step initial resetInput) pins k).r0_nstate = 0 ∧
      (pins k).nio_5Freq_5Fvalid = 1 ∧ MulDivCheckedHistory.legal (pins k) ∧
      MulDivCheckedHistory.captured (run (step initial resetInput) pins n) =
        MulDivCheckedHistory.requestView (pins k) ∧
      ∀ t, k ≤ t → t < n → (pins t).nreset = 0 ∧ (pins t).nio_5Fkill = 0 ∧
        ((observe (run (step initial resetInput) pins t) (pins t)).nio_5Fresp_5Fvalid = 0 ∨
          (pins t).nio_5Fresp_5Fready = 0) := by
  induction n with
  | zero =>
    have cleared := (MulDivCheckedHistory.reset_monitors initial resetInput reset).1
    change (step initial resetInput).r9_ncontractPending = 1 at pending
    rw [cleared] at pending
    contradiction
  | succ n ih =>
    have edge := pending_edge (run (step initial resetInput) pins n) (pins n) pending
    by_cases accepted : (run (step initial resetInput) pins n).r0_nstate = 0 ∧ (pins n).nio_5Freq_5Fvalid = 1
    · refine ⟨n, by omega, accepted.1, accepted.2,
        accepted_legal _ _ accepted.1 accepted.2 pending,
        MulDivCheckedHistory.capture _ _ accepted.1 accepted.2, ?_⟩
      intro t low high
      have equal : t = n := by omega
      subst t
      exact ⟨edge.1, edge.2.1, pending_not_acknowledged _ _ pending⟩
    · have oldPending : (run (step initial resetInput) pins n).r9_ncontractPending = 1 :=
        edge.2.2.resolve_left accepted
      obtain ⟨k, before, ready, valid, legal, captured, uninterrupted⟩ := ih oldPending
      refine ⟨k, by omega, ready, valid, legal, ?_, ?_⟩
      · change MulDivCheckedHistory.captured (step _ _) = _
        rw [MulDivCheckedControl.pending_history_stable _ _
          (MulDivCheckedControl.run_invariant initial resetInput reset pins n) oldPending, captured]
      · intro t low high
        by_cases last : t = n
        · subst t
          exact ⟨edge.1, edge.2.1, pending_not_acknowledged _ _ pending⟩
        · exact uninterrupted t low (by omega)

end MulDivCheckedOrigin
