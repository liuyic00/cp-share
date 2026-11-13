import Proofs.MulDivCheckedHistory

namespace MulDivCheckedMetadata
open nMulDivChecked

/-- An outstanding monitored request has matching core
metadata, even when the live request pins change during execution. -/
def Invariant (s : State) : Prop := s.r9_ncontractPending = 1 →
  s.r2_nreq_5Ftag = s.r15_ncontractTag ∧ s.r1_nreq_5Fdw = s.r12_ncontractDw

theorem reset_invariant (s : State) (i : Inputs) (reset : i.nreset = 1) :
    Invariant (step s i) := by
  simp [Invariant, step, eval, reset]

theorem step_invariant (s : State) (i : Inputs) (previous : Invariant s) :
    Invariant (step s i) := by
  simp only [Invariant, step, eval] at *
  bv_decide

theorem run_invariant (initial : State) (resetInput : Inputs) (reset : resetInput.nreset = 1)
    (pins : Nat → Inputs) (n : Nat) : Invariant (run (step initial resetInput) pins n) := by
  induction n with
  | zero => exact reset_invariant initial resetInput reset
  | succ n ih => exact step_invariant _ _ ih

/-- The third exported assertion checks the tag of the accepted request. -/
theorem tag_assertion (s : State) (i : Inputs) (metadata : Invariant s) :
    (eval s i).assertions[2]! = true := by
  simp only [Invariant] at metadata
  simp only [eval, List.getElem!_cons_zero, List.getElem!_cons_succ]
  bv_decide

theorem tag_assertion_after_reset (initial : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (pins : Nat → Inputs) (n : Nat) :
    (eval (run (step initial resetInput) pins n) (pins n)).assertions[2]! = true :=
  tag_assertion _ _ (run_invariant initial resetInput reset pins n)

/-- Legality is captured with the request and retained until cancellation or
acknowledgement. The bit-vector form is convenient for control proofs. -/
def LegalInvariant (s : State) : Prop := s.r9_ncontractPending = 1 →
  s.r11_ncontractFn < 8#4 ∧
    (s.r12_ncontractDw = 1 ∨ s.r11_ncontractFn = 0 ∨ 4#4 ≤ s.r11_ncontractFn)

theorem legal_reset (s : State) (i : Inputs) (reset : i.nreset = 1) :
    LegalInvariant (step s i) := by
  simp [LegalInvariant, step, eval, reset]

theorem legal_step (s : State) (i : Inputs) (previous : LegalInvariant s) :
    LegalInvariant (step s i) := by
  simp only [LegalInvariant, step, eval] at *
  bv_decide

theorem legal_run (initial : State) (resetInput : Inputs) (reset : resetInput.nreset = 1)
    (pins : Nat → Inputs) (n : Nat) : LegalInvariant (run (step initial resetInput) pins n) := by
  induction n with
  | zero => exact legal_reset initial resetInput reset
  | succ n ih => exact legal_step _ _ ih

end MulDivCheckedMetadata
