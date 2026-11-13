import Proofs.MulDivCheckedMulFuture
import Proofs.MulDivCheckedMulTiming
import Proofs.MulDivCheckedMetadata

namespace MulDivCheckedMulTrace
open nMulDivChecked
open MulDivCheckedMulSpec (specification)

def Invariant (s : State) : Prop := s.r9_ncontractPending = 1 → s.r11_ncontractFn < 4#4 →
  (s.r0_nstate = 2 → MulDivCheckedMulFuture.Computing s) ∧
  (s.r0_nstate = 6 → ∀ i : Inputs, (observe s i).nio_5Fresp_5Fbits_5Fdata =
    specification (MulDivCheckedHistory.captured s))

theorem reset_invariant (s : State) (i : Inputs) (reset : i.nreset = 1) :
    Invariant (step s i) := by simp [Invariant, step, eval, reset]

theorem step_invariant (s : State) (i : Inputs) (previous : Invariant s)
    (timing : MulDivCheckedMulTiming.Invariant s) : Invariant (step s i) := by
  intro pending operation
  have pins : i.nreset = 0 ∧ i.nio_5Fkill = 0 := by
    simp only [step, eval] at pending
    bv_decide
  by_cases idle : s.r0_nstate = 0
  · have valid : i.nio_5Freq_5Fvalid = 1 := by
      simp only [MulDivCheckedMulTiming.Invariant, MulDivCheckedMulTiming.cycles, MulDivCheckedMulTiming.offset] at timing
      simp only [step, eval, idle] at pending operation
      bv_decide
    have legal : MulDivCheckedMulSpec.Legal (MulDivCheckedProjection.inputs i) := by
      simp only [MulDivCheckedMulSpec.Legal, MulDivCheckedProjection.inputs]
      simp only [step, eval, idle, valid] at pending operation
      bv_decide
    refine ⟨fun _ => MulDivCheckedMulFuture.capture_computing s i idle valid pins.1 pins.2 legal, ?_⟩
    intro done
    simp only [step, eval, idle, valid] at done
    bv_decide
  · have oldPending : s.r9_ncontractPending = 1 := by
      simp only [step, eval] at pending
      bv_decide
    have oldOperation : s.r11_ncontractFn < 4#4 := by
      simp only [step, eval] at operation
      bv_decide
    have phases := timing oldPending oldOperation
    have oldCorrect := previous oldPending oldOperation
    have control : (s.r0_nstate = 2 ∧ s.r3_ncount < 64#7) ∨ s.r0_nstate = 6 := by
      simp only [MulDivCheckedMulTiming.cycles, MulDivCheckedMulTiming.offset] at phases
      bv_decide
    constructor
    · intro computing
      have predecessor : s.r0_nstate = 2 ∧ s.r3_ncount < 63#7 := by
        simp only [step, eval] at computing
        bv_decide
      exact MulDivCheckedMulFuture.computing_step s i predecessor.1 predecessor.2 pins.1 pins.2
        (oldCorrect.1 predecessor.1)
    · intro done later
      have predecessor : (s.r0_nstate = 2 ∧ s.r3_ncount = 63) ∨ s.r0_nstate = 6 := by
        simp only [step, eval] at done
        bv_decide
      rcases predecessor with ⟨state, count⟩ | state
      · exact MulDivCheckedMulFuture.computing_last s i later state count pins.1 pins.2 (oldCorrect.1 state)
      · have stalled : i.nio_5Fresp_5Fready = 0 := by
          simp only [step, eval, state] at pending
          bv_decide
        have stable := MulDivControl.stall_stable (MulDivCheckedProjection.state s)
          (MulDivCheckedProjection.inputs i) (MulDivCheckedProjection.inputs later)
          (Or.inl state) pins.1 pins.2 stalled
        have data : (observe (step s i) later).nio_5Fresp_5Fbits_5Fdata =
            (observe s i).nio_5Fresp_5Fbits_5Fdata := stable.2.1
        rw [data, oldCorrect.2 state i, MulDivCheckedHistory.hold s i (Or.inl (by rw [state]; decide))]

theorem run_invariant (initial : State) (resetInput : Inputs) (reset : resetInput.nreset = 1)
    (pins : Nat → Inputs) (n : Nat) : Invariant (run (step initial resetInput) pins n) := by
  induction n with
  | zero => exact reset_invariant initial resetInput reset
  | succ n ih =>
    exact step_invariant _ _ ih (MulDivCheckedMulTiming.run_invariant initial resetInput reset pins n)

end MulDivCheckedMulTrace
