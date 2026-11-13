import Proofs.MulDivCheckedWitness

namespace MulDivCheckedDivisionTrace
open nMulDivChecked
open MulDivCheckedDivisionInit (Operation Phases Initialized)
open MulDivCheckedMagnitude (Computing Correct parameters)

def Invariant (s : State) : Prop := s.r9_ncontractPending = 1 → Operation s →
  (s.r0_nstate = 3 → Computing s) ∧
  (s.r0_nstate = 5 → Correct (MulDivCheckedProjection.state s) (parameters s).1 (parameters s).2) ∧
  (s.r0_nstate = 7 → MulDivCheckedWitness.Invariant s)

private theorem initialized_zero (s : State) (phases : Phases s)
    (state : s.r0_nstate = 3) (count : s.r3_ncount = 0) : Initialized s := by
  simp [Phases, state, count] at phases
  exact phases.2

private theorem phase_control (s : State) (phases : Phases s) :
    (s.r0_nstate = 1 ∧ s.r3_ncount = 0) ∨
    (s.r0_nstate = 3 ∧ s.r3_ncount ≤ 64#7 ∧ s.r16_ncontractWasNegated = 0) ∨
    s.r0_nstate = 5 ∨ s.r0_nstate = 7 := by
  rcases phases with ⟨st, _, count, _⟩ | ⟨st, count, flag, _⟩ | ⟨st, _⟩ | st
  · exact Or.inl ⟨st, count⟩
  · exact Or.inr (Or.inl ⟨st, count, flag⟩)
  · exact Or.inr (Or.inr (Or.inl st))
  · exact Or.inr (Or.inr (Or.inr st))

private theorem pending_pins (s : State) (i : Inputs) (pending : (step s i).r9_ncontractPending = 1) :
    i.nreset = 0 ∧ i.nio_5Fkill = 0 := by
  simp only [step, eval] at pending
  bv_decide

theorem reset_invariant (s : State) (i : Inputs) (reset : i.nreset = 1) :
    Invariant (step s i) := by simp [Invariant, step, eval, reset]

theorem step_invariant (s : State) (i : Inputs)
    (initialization : MulDivCheckedDivisionInit.Invariant s) (previous : Invariant s) :
    Invariant (step s i) := by
  intro pending operation
  have pins := pending_pins s i pending
  have nextPhases := MulDivCheckedDivisionInit.step_invariant s i initialization pending operation
  have nextControl := phase_control _ nextPhases
  by_cases idle : s.r0_nstate = 0
  · have control : (step s i).r0_nstate = 1 ∨
        ((step s i).r0_nstate = 3 ∧ (step s i).r3_ncount = 0) := by
      simp only [step, eval, idle, Operation] at pending operation nextControl ⊢
      bv_decide
    refine ⟨?_, ?_, ?_⟩
    · intro state
      have count : (step s i).r3_ncount = 0 := by rcases control with h | h; simp_all; exact h.2
      exact MulDivCheckedMagnitude.initialized_computing _ state count (initialized_zero _ nextPhases state count)
    · intro state
      rcases control with h | h <;> simp_all
    · intro state
      rcases control with h | h <;> simp_all
  · have oldPending : s.r9_ncontractPending = 1 := by
      simp only [step, eval] at pending
      bv_decide
    have oldOperation : Operation s := by
      simp only [Operation, step, eval] at operation ⊢
      bv_decide
    have oldPhases := initialization oldPending oldOperation
    have oldControl := phase_control s oldPhases
    have oldCorrect := previous oldPending oldOperation
    refine ⟨?_, ?_, ?_⟩
    · intro state
      by_cases zero : (step s i).r3_ncount = 0
      · exact MulDivCheckedMagnitude.initialized_computing _ state zero (initialized_zero _ nextPhases state zero)
      · have predecessor : s.r0_nstate = 3 ∧ s.r3_ncount < 64#7 := by
          simp only [step, eval] at state zero
          bv_decide
        exact MulDivCheckedMagnitude.computing_step s i predecessor.1 predecessor.2 pins.1 pins.2
          (oldCorrect.1 predecessor.1)
    · intro state
      have predecessor : s.r0_nstate = 3 ∧ s.r3_ncount = 64 := by
        simp only [step, eval] at state
        bv_decide
      exact MulDivCheckedMagnitude.computing_last s i predecessor.1 predecessor.2 pins.1 pins.2
        (oldCorrect.1 predecessor.1)
    · intro state
      have predecessor : (s.r0_nstate = 3 ∧ s.r3_ncount = 64) ∨ s.r0_nstate = 5 ∨ s.r0_nstate = 7 := by
        simp only [step, eval] at state
        bv_decide
      rcases predecessor with ⟨dividing, last⟩ | negating | done
      · have flag : (step s i).r16_ncontractWasNegated = 0 := by
          simp only [step, eval, dividing]
          bv_decide
        exact MulDivCheckedWitness.from_raw _ flag
          (MulDivCheckedMagnitude.computing_last s i dividing last pins.1 pins.2 (oldCorrect.1 dividing))
      · exact MulDivCheckedWitness.negation_preserves s i negating pins.1 (oldCorrect.2.1 negating)
      · exact MulDivCheckedWitness.done_preserves s i done pins.1 (oldCorrect.2.2 done)

theorem run_invariant (initial : State) (resetInput : Inputs) (reset : resetInput.nreset = 1)
    (pins : Nat → Inputs) (n : Nat) : Invariant (run (step initial resetInput) pins n) := by
  induction n with
  | zero => exact reset_invariant initial resetInput reset
  | succ n ih =>
    exact step_invariant _ _ (MulDivCheckedDivisionInit.run_invariant initial resetInput reset pins n) ih

theorem witness_after_reset (initial : State) (resetInput : Inputs) (reset : resetInput.nreset = 1)
    (pins : Nat → Inputs) (n : Nat)
    (pending : (run (step initial resetInput) pins n).r9_ncontractPending = 1)
    (operation : Operation (run (step initial resetInput) pins n))
    (done : (run (step initial resetInput) pins n).r0_nstate = 7) :
    MulDivCheckedWitness.Invariant (run (step initial resetInput) pins n) :=
  (run_invariant initial resetInput reset pins n pending operation).2.2 done

end MulDivCheckedDivisionTrace
