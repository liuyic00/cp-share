import Proofs.MulDivCheckedOrigin

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

theorem run_offset (s : State) (inputs : Nat → Inputs) (start n : Nat) :
    run s inputs (start + n) = run (run s inputs start) (fun t => inputs (start + t)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step (run s inputs (start + n)) (inputs (start + n)) = _
    rw [ih]
    rfl

theorem run_congr (s : State) (a b : Nat → Inputs) (n : Nat)
    (same : ∀ t, t < n → a t = b t) : run s a n = run s b n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run, run, same n (by omega), ih (by intro t h; exact same t (by omega))]

theorem pending_at (s : State) (inputs : Nat → Inputs) (start finish : Nat)
    (pending : (run s inputs finish).r9_ncontractPending = 1)
    (noCapture : ∀ t, start ≤ t → t < finish → v2 (run s inputs t) (inputs t) ≠ 1)
    (t : Nat) (lower : start ≤ t) (upper : t ≤ finish) :
    (run s inputs t).r9_ncontractPending = 1 := by
  induction finish with
  | zero =>
    have h : t = 0 := by omega
    subst t
    exact pending
  | succ finish ih =>
    by_cases last : t = finish + 1
    · subst t
      exact pending
    · have oldPending : (run s inputs finish).r9_ncontractPending = 1 := by
        have edge := (pending_edge _ _ pending).2.2
        rcases edge with captured | held
        · exact (noCapture finish (by omega) (by omega) captured.1).elim
        · exact held.2
      exact ih oldPending (by intro u lo hi; exact noCapture u lo (by omega)) (by omega)

/-- A still-pending transaction cannot have accepted an earlier response. -/
theorem pending_response_blocked (s : State) (i : Inputs)
    (nextPending : (step s i).r9_ncontractPending = 1)
    (noCapture : v2 s i ≠ 1) (response : v38 s i = 1) :
    i.nio_5Fresp_5Fready = 0 := by
  rw [pending_transition] at nextPending
  bv_decide

theorem core_output_input_independent (s : State) (i j : Inputs) :
    observe s i = observe s j := by
  simp only [observe, eval_eq_spec, evalSpec]
  rfl

theorem pending_response_stable (s : State) (inputs : Nat → Inputs) (start finish : Nat)
    (pending : (run s inputs finish).r9_ncontractPending = 1)
    (noCapture : ∀ t, start ≤ t → t < finish → v2 (run s inputs t) (inputs t) ≠ 1)
    (response : v38 (run s inputs start) (inputs start) = 1)
    (t : Nat) (lower : start ≤ t) (upper : t ≤ finish) :
    v38 (run s inputs t) (inputs t) = 1 ∧
      coreState (run s inputs t) = coreState (run s inputs start) := by
  induction t with
  | zero =>
    have h : start = 0 := by omega
    subst start
    exact ⟨response, rfl⟩
  | succ t ih =>
    by_cases first : start = t + 1
    · subst start
      exact ⟨response, rfl⟩
    · obtain ⟨valid, stable⟩ := ih (by omega) (by omega)
      have nextPending := pending_at s inputs start finish pending noCapture (t + 1) (by omega) upper
      have edge := pending_edge _ _ nextPending
      have blocked := pending_response_blocked _ _ nextPending (noCapture t (by omega) (by omega)) valid
      have output := stalled_output (run s inputs t) (inputs t) (inputs (t + 1)) valid blocked edge.2.1 edge.1
      exact ⟨output.1, (stalled_core _ _ valid blocked edge.2.1 edge.1).trans stable⟩

theorem outputs_of_core_eq (s t : State) (i j : Inputs) (same : coreState s = coreState t) :
    coreOutputs (observe s i) = coreOutputs (observe t j) := by
  rw [core_observe, core_observe, same]
  simp only [Core.observe, DesignnMulDiv.nMulDiv.eval_eq_spec, DesignnMulDiv.nMulDiv.evalSpec]
  rfl

theorem pending_data_stable (s : State) (inputs : Nat → Inputs) (start finish : Nat)
    (pending : (run s inputs finish).r9_ncontractPending = 1)
    (noCapture : ∀ t, start ≤ t → t < finish → v2 (run s inputs t) (inputs t) ≠ 1)
    (response : v38 (run s inputs start) (inputs start) = 1) (ordered : start ≤ finish) :
    (observe (run s inputs finish) (inputs finish)).nio_5Fresp_5Fbits_5Fdata =
      (observe (run s inputs start) (inputs start)).nio_5Fresp_5Fbits_5Fdata := by
  have stable := (pending_response_stable s inputs start finish pending noCapture response finish ordered (by omega)).2
  exact congrArg (fun output => output.nio_5Fresp_5Fbits_5Fdata)
    (outputs_of_core_eq _ _ (inputs finish) (inputs start) stable)

end HierarchicalMulDivChecked
