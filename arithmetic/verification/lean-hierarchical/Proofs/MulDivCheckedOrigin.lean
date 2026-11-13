import Proofs.MulDivCheckedStability

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

def requestData (i : Inputs) : Inputs :=
  { i with nreset := 0, nio_5Freq_5Fvalid := 1, nio_5Fkill := 0, nio_5Fresp_5Fready := 0 }

theorem pending_edge (s : State) (i : Inputs) (pending : (step s i).r9_ncontractPending = 1) :
    i.nreset = 0 ∧ i.nio_5Fkill = 0 ∧
      ((v2 s i = 1 ∧ v160 s i = 1) ∨ (v2 s i ≠ 1 ∧ s.r9_ncontractPending = 1)) := by
  rw [pending_transition] at pending
  have killed : i.nio_5Fkill = 1 → v160 s i = 0 := by
    simp only [v160, v159, v31]
    bv_decide
  bv_decide

/-- Each monitored transaction originates at a legal acceptance edge.
    Every subsequent edge in the witness is free of reset, kill, and capture. -/
theorem pending_origin (s : State) (resetInput : Inputs) (inputs : Nat → Inputs)
    (reset : resetInput.nreset = 1) (n : Nat)
    (pending : (run (step s resetInput) inputs n).r9_ncontractPending = 1) :
    ∃ k, k < n ∧
      (run (step s resetInput) inputs k).r0_nstate = 0 ∧
      (inputs k).nio_5Freq_5Fvalid = 1 ∧ legalArithmetic (inputs k) ∧
      (inputs k).nreset = 0 ∧ (inputs k).nio_5Fkill = 0 ∧
      recordedRequest (run (step s resetInput) inputs n) = requestData (inputs k) ∧
      (∀ t, k < t → t < n → (inputs t).nreset = 0 ∧ (inputs t).nio_5Fkill = 0 ∧
        v2 (run (step s resetInput) inputs t) (inputs t) ≠ 1) := by
  induction n with
  | zero =>
    simp [run, step, eval_eq_spec, evalSpec, reset, v8] at pending
  | succ n ih =>
    obtain ⟨noReset, noKill, captured | held⟩ := pending_edge _ _ pending
    · have acceptance : (run (step s resetInput) inputs n).r0_nstate = 0 ∧
          (inputs n).nio_5Freq_5Fvalid = 1 := by
        have h := captured.1
        simp only [v2, v1, v0] at h
        bv_decide
      refine ⟨n, by omega, acceptance.1, acceptance.2,
        monitor_accepts_legal _ _ captured.2, noReset, noKill, ?_, ?_⟩
      · exact recorded_capture _ _ captured.1
      · intro t after before
        omega
    · obtain ⟨k, before, idle, valid, legal, r, kill, record, uninterrupted⟩ := ih held.2
      refine ⟨k, by omega, idle, valid, legal, r, kill, ?_, ?_⟩
      · rw [run, recorded_hold _ _ held.1]
        exact record
      · intro t after bound
        by_cases last : t = n
        · subst t
          exact ⟨noReset, noKill, held.1⟩
        · exact uninterrupted t after (by omega)

end HierarchicalMulDivChecked
