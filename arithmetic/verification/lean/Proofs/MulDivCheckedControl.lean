import Proofs.MulDivCheckedHistory

namespace MulDivCheckedControl
open nMulDivChecked

/-- An uncancelled monitored request occupies a reachable execution phase.
The division counter bound includes the final quotient-bit iteration. -/
def Active (s : State) : Prop :=
  (s.r0_nstate = 1 ∧ s.r3_ncount = 0) ∨
  (s.r0_nstate = 2 ∧ s.r3_ncount < 64#7) ∨
  (s.r0_nstate = 3 ∧ s.r3_ncount ≤ 64#7) ∨
  s.r0_nstate = 5 ∨ s.r0_nstate = 6 ∨ s.r0_nstate = 7

def Invariant (s : State) : Prop := s.r9_ncontractPending = 1 → Active s

theorem reset_invariant (s : State) (i : Inputs) (reset : i.nreset = 1) :
    Invariant (step s i) := by
  simp [Invariant, step, eval, reset]

theorem step_invariant (s : State) (i : Inputs) (previous : Invariant s) :
    Invariant (step s i) := by
  simp only [Invariant, Active, step, eval] at *
  bv_decide

theorem run_invariant (initial : State) (resetInput : Inputs) (reset : resetInput.nreset = 1)
    (pins : Nat → Inputs) (n : Nat) : Invariant (run (step initial resetInput) pins n) := by
  induction n with
  | zero => exact reset_invariant initial resetInput reset
  | succ n ih => exact step_invariant _ _ ih

theorem active_not_idle (s : State) (active : Active s) : s.r0_nstate ≠ 0 := by
  simp only [Active] at active
  bv_decide

/-- Live request pins cannot overwrite captured operands while the monitored
transaction remains outstanding. -/
theorem pending_history_stable (s : State) (i : Inputs) (control : Invariant s)
    (pending : s.r9_ncontractPending = 1) :
    MulDivCheckedHistory.captured (step s i) = MulDivCheckedHistory.captured s :=
  MulDivCheckedHistory.hold s i (Or.inl (active_not_idle s (control pending)))

end MulDivCheckedControl
