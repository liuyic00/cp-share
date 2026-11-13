import Proofs.MulDivCheckedLatency

namespace MulDivCheckedUnsignedTiming
open nMulDivChecked

def Operation (s : State) : Prop := s.r11_ncontractFn = 5 ∨ s.r11_ncontractFn = 7

/-- Unsigned division runs exactly 65 restoring iterations; there are no
input or output negation phases, including for a zero divisor. -/
def Invariant (s : State) : Prop :=
  s.r9_ncontractPending = 1 → Operation s →
    (s.r0_nstate = 3 ∧ s.r3_ncount = s.r10_ncontractAge ∧
      s.r10_ncontractAge ≤ 64#7 ∧ s.r4_nneg_5Fout = 0) ∨
    (s.r0_nstate = 7 ∧ s.r10_ncontractAge = 65)

theorem reset_invariant (s : State) (i : Inputs) (reset : i.nreset = 1) :
    Invariant (step s i) := by
  simp [Invariant, step, eval, reset]

theorem step_invariant (s : State) (i : Inputs) (previous : Invariant s) :
    Invariant (step s i) := by
  simp only [Invariant, Operation, step, eval] at *
  bv_decide

theorem run_invariant (initial : State) (resetInput : Inputs) (reset : resetInput.nreset = 1)
    (pins : Nat → Inputs) (n : Nat) : Invariant (run (step initial resetInput) pins n) := by
  induction n with
  | zero => exact reset_invariant initial resetInput reset
  | succ n ih => exact step_invariant _ _ ih

theorem unsigned_latency (s : State) (operation : Operation s) :
    MulDivCheckedLatency.latency s = 65 := by
  simp only [Operation] at operation
  rcases operation with operation | operation <;>
    simp [MulDivCheckedLatency.latency, MulDivCheckedLatency.negative,
      MulDivCheckedLatency.signedBit, MulDivCheckedLatency.outputNegative, operation]

theorem timing_assertions (s : State) (i : Inputs) (invariant : Invariant s)
    (operation : Operation s) :
    ((eval s i).assertions.take 2).all id = true := by
  rw [MulDivCheckedLatency.timing_checks, unsigned_latency s operation]
  simp only [Invariant, Operation] at invariant operation
  simp only [MulDivCheckedLatency.gate, observe, eval, List.all_cons, List.all_nil, id_eq]
  simp only [← BitVec.le_def]
  bv_decide

theorem timing_assertions_after_reset (initial : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (pins : Nat → Inputs) (n : Nat)
    (operation : Operation (run (step initial resetInput) pins n)) :
    ((eval (run (step initial resetInput) pins n) (pins n)).assertions.take 2).all id = true :=
  timing_assertions _ _ (run_invariant initial resetInput reset pins n) operation

end MulDivCheckedUnsignedTiming
