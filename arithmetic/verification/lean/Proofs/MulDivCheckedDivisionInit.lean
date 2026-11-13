import Proofs.MulDivCheckedLatency

namespace MulDivCheckedDivisionInit
open nMulDivChecked
open MulDivCheckedLatency (operand negative magnitude)
set_option maxHeartbeats 2000000

def Operation (s : State) : Prop :=
  s.r11_ncontractFn = 4 ∨ s.r11_ncontractFn = 5 ∨ s.r11_ncontractFn = 6 ∨ s.r11_ncontractFn = 7

def Initialized (s : State) : Prop :=
  s.r8_nremainder = 0#66 ++ magnitude s s.r13_ncontractA ∧
  s.r7_ndivisor = 0#1 ++ magnitude s s.r14_ncontractB

def Phases (s : State) : Prop :=
  (s.r0_nstate = 1 ∧ (s.r11_ncontractFn = 4 ∨ s.r11_ncontractFn = 6) ∧ s.r3_ncount = 0 ∧ s.r16_ncontractWasNegated = 0 ∧
    s.r8_nremainder = 0#66 ++ operand s s.r13_ncontractA ∧
    s.r7_ndivisor = negative s s.r14_ncontractB ++ operand s s.r14_ncontractB ∧ s.r6_nresHi = 0) ∨
  (s.r0_nstate = 3 ∧ s.r3_ncount ≤ 64#7 ∧ s.r16_ncontractWasNegated = 0 ∧
    (s.r3_ncount = 0 → Initialized s)) ∨
  (s.r0_nstate = 5 ∧ s.r16_ncontractWasNegated = 0) ∨ s.r0_nstate = 7

def Invariant (s : State) : Prop := s.r9_ncontractPending = 1 → Operation s → Phases s

theorem reset_invariant (s : State) (i : Inputs) (reset : i.nreset = 1) :
    Invariant (step s i) := by simp [Invariant, step, eval, reset]

theorem step_invariant (s : State) (i : Inputs) (previous : Invariant s) :
    Invariant (step s i) := by
  intro pending operation
  by_cases idle : s.r0_nstate = 0
  · simp only [Invariant, Operation, Phases, Initialized, magnitude, negative, operand,
      MulDivCheckedLatency.signedBit, step, eval, idle] at *
    bv_decide
  · have oldPending : s.r9_ncontractPending = 1 := by
      simp only [step, eval] at pending
      bv_decide
    have oldOperation : Operation s := by
      simp only [Operation, step, eval] at operation ⊢
      bv_decide
    have phases := previous oldPending oldOperation
    rcases phases with ⟨state, facts⟩ | ⟨state, facts⟩ | ⟨state, facts⟩ | state <;>
      simp only [Invariant, Operation, Phases, Initialized, magnitude, negative, operand,
        MulDivCheckedLatency.signedBit, step, eval, state] at * <;> bv_decide

theorem run_invariant (initial : State) (resetInput : Inputs) (reset : resetInput.nreset = 1)
    (pins : Nat → Inputs) (n : Nat) : Invariant (run (step initial resetInput) pins n) := by
  induction n with
  | zero => exact reset_invariant initial resetInput reset
  | succ n ih => exact step_invariant _ _ ih

end MulDivCheckedDivisionInit
