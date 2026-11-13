import Proofs.MulDivCheckedProjection
import Proofs.MulDivControl

namespace MulDivCheckedStall
open nMulDivChecked

private theorem and_left (x y : BitVec 1) (h : x &&& y = 1) : x = 1 := by bv_decide

private theorem stall_origin (s : State) (i : Inputs)
    (flag : (step s i).r21_ncontractWasStalled = 1) :
    (s.r0_nstate = 6 ∨ s.r0_nstate = 7) ∧ i.nreset = 0 ∧
      i.nio_5Fkill = 0 ∧ i.nio_5Fresp_5Fready = 0 := by
  simp only [step, eval] at flag
  bv_decide

/-- The recorded stall flag implies stable actual response data on the next
cycle, from arbitrary registers and with arbitrary later input pins. -/
theorem stable_after_recorded_stall (s : State) (i later : Inputs)
    (flag : (step s i).r21_ncontractWasStalled = 1) :
    (observe (step s i) later).nio_5Fresp_5Fvalid = 1 ∧
    (observe (step s i) later).nio_5Fresp_5Fbits_5Fdata = (step s i).r19_ncontractPreviousData ∧
    (observe (step s i) later).nio_5Fresp_5Fbits_5Ftag = (step s i).r20_ncontractPreviousTag := by
  have origin := stall_origin s i flag
  have stable := MulDivControl.stall_stable (MulDivCheckedProjection.state s)
    (MulDivCheckedProjection.inputs i) (MulDivCheckedProjection.inputs later)
    origin.1 origin.2.1 origin.2.2.1 origin.2.2.2
  have next : MulDivCheckedProjection.outputs (observe (step s i) later) =
      nMulDiv.observe (nMulDiv.step (MulDivCheckedProjection.state s)
        (MulDivCheckedProjection.inputs i)) (MulDivCheckedProjection.inputs later) := by
    rw [MulDivCheckedProjection.observe_projects, MulDivCheckedProjection.step_projects]
  rw [← next, ← MulDivCheckedProjection.observe_projects s i] at stable
  exact stable

def gate (s : State) (i : Inputs) : BitVec 1 :=
  (s.r21_ncontractWasStalled &&& (i.nio_5Fkill ^^^ 1)) &&& (i.nreset ^^^ 1)

private theorem last_checks (s : State) (i : Inputs)
    (correct : s.r21_ncontractWasStalled = 1 →
      (observe s i).nio_5Fresp_5Fvalid = 1 ∧
      (observe s i).nio_5Fresp_5Fbits_5Fdata = s.r19_ncontractPreviousData ∧
      (observe s i).nio_5Fresp_5Fbits_5Ftag = s.r20_ncontractPreviousTag) :
    ((eval s i).assertions.drop 8).all id = true := by
  change ([decide (gate s i ≠ 1 ∨ (observe s i).nio_5Fresp_5Fvalid = 1),
    decide (gate s i ≠ 1 ∨ (if (observe s i).nio_5Fresp_5Fbits_5Fdata = s.r19_ncontractPreviousData then (1 : BitVec 1) else 0) = 1),
    decide (gate s i ≠ 1 ∨ (if (observe s i).nio_5Fresp_5Fbits_5Ftag = s.r20_ncontractPreviousTag then (1 : BitVec 1) else 0) = 1)]).all id = true
  by_cases enabled : gate s i = 1
  · have flag : s.r21_ncontractWasStalled = 1 := and_left _ _ (and_left _ _ enabled)
    have facts := correct flag
    simp only [facts.1, facts.2.1, facts.2.2, if_true]
    simp
  · simp
    exact ⟨Or.inl enabled, Or.inl enabled, Or.inl enabled⟩

/-- All three exported response-stall assertions hold after every edge. -/
theorem stall_assertions (s : State) (i later : Inputs) :
    ((eval (step s i) later).assertions.drop 8).all id = true :=
  last_checks _ _ (stable_after_recorded_stall s i later)

/-- The exported stall checks hold at every observation after the initial edge,
including arbitrary later resets, kills, requests, and response readiness. -/
theorem stall_assertions_trace (initial : State) (first : Inputs)
    (pins : Nat → Inputs) (n : Nat) :
    ((eval (run (step initial first) pins n) (pins n)).assertions.drop 8).all id = true := by
  cases n with
  | zero => exact stall_assertions initial first (pins 0)
  | succ n => exact stall_assertions (run (step initial first) pins n) (pins n) (pins (n + 1))

end MulDivCheckedStall
