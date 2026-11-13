import Proofs.MulDivCheckedRequest

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

theorem age_transition (s : State) (i : Inputs) :
    (step s i).r10_ncontractAge =
      if i.nreset = 1 then 0 else if v2 s i = 1 then 0 else
        if s.r9_ncontractPending = 1 ∧ v38 s i = 0 then
          s.r10_ncontractAge + 1 else s.r10_ncontractAge := by
  simp only [step, eval_eq_spec, evalSpec, v168, v167, v166, v165, v164, v31, v68, v82]
  bv_decide

theorem pending_transition (s : State) (i : Inputs) :
    (step s i).r9_ncontractPending =
      if i.nreset = 1 then 0 else if v2 s i = 1 then v160 s i else
        if i.nio_5Fkill = 1 ∨ (i.nio_5Fresp_5Fready = 1 ∧ v38 s i = 1)
          then 0 else s.r9_ncontractPending := by
  simp only [step, eval_eq_spec, evalSpec, v8, v163, v162, v161, v40, v39, v31]
  bv_decide

theorem cancel_pending (s : State) (i : Inputs) (kill : i.nio_5Fkill = 1) :
    (step s i).r9_ncontractPending = 0 := by
  rw [pending_transition]
  simp only [v160, v159, v31, kill]
  bv_decide

theorem age_capture (s : State) (i : Inputs) (capture : v2 s i = 1) :
    (step s i).r10_ncontractAge = 0 := by
  rw [age_transition]
  simp [capture]

theorem age_compute (s : State) (i : Inputs) (reset : i.nreset = 0)
    (noCapture : v2 s i ≠ 1) (pending : s.r9_ncontractPending = 1)
    (notDone : v38 s i = 0) :
    (step s i).r10_ncontractAge = s.r10_ncontractAge + 1 := by
  rw [age_transition]
  simp [reset, noCapture, pending, notDone]
  intro impossible
  exact (noCapture impossible).elim

theorem age_response (s : State) (i : Inputs) (reset : i.nreset = 0)
    (noCapture : v2 s i ≠ 1) (done : v38 s i = 1) :
    (step s i).r10_ncontractAge = s.r10_ncontractAge := by
  rw [age_transition]
  simp [reset, noCapture, done]
  intro impossible
  exact (noCapture impossible).elim

/-- Age starts at zero after acceptance, so it counts subsequent computation
    edges; the complete request latency includes the acceptance edge. -/
theorem age_computing_trace (s : State) (inputs : Nat → Inputs) (n : Nat)
    (initial : s.r10_ncontractAge = 0)
    (computing : ∀ t, t < n →
      (inputs t).nreset = 0 ∧ v2 (run s inputs t) (inputs t) ≠ 1 ∧
      (run s inputs t).r9_ncontractPending = 1 ∧ v38 (run s inputs t) (inputs t) = 0) :
    (run s inputs n).r10_ncontractAge = BitVec.ofNat 7 n := by
  induction n with
  | zero => exact initial
  | succ n ih =>
    obtain ⟨reset, capture, pending, ready⟩ := computing n (by omega)
    rw [run, age_compute _ _ reset capture pending ready,
      ih (by intro t h; exact computing t (by omega))]
    exact (BitVec.ofNat_add n 1).symm

end HierarchicalMulDivChecked
