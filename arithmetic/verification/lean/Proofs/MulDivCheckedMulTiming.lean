import Proofs.MulDivCheckedLatency

namespace MulDivCheckedMulTiming
open nMulDivChecked

def cycles (s : State) : BitVec 7 := if s.r12_ncontractDw = 1 then 64 else 32

def offset (s : State) : BitVec 7 := if s.r12_ncontractDw = 1 then 0 else 32

/-- Multiplication's monitor age tracks its actual iteration counter, including
the word operation's initial counter offset and completion stalls. -/
def Invariant (s : State) : Prop :=
  s.r9_ncontractPending = 1 → s.r11_ncontractFn < 4#4 →
    (s.r0_nstate = 2 ∧ s.r3_ncount = s.r10_ncontractAge + offset s ∧ s.r10_ncontractAge < cycles s) ∨
    (s.r0_nstate = 6 ∧ s.r10_ncontractAge = cycles s)

theorem reset_invariant (s : State) (i : Inputs) (reset : i.nreset = 1) :
    Invariant (step s i) := by
  simp [Invariant, step, eval, reset]

theorem step_invariant (s : State) (i : Inputs) (previous : Invariant s) :
    Invariant (step s i) := by
  simp only [Invariant, cycles, offset, step, eval] at *
  bv_decide

theorem run_invariant (initial : State) (resetInput : Inputs) (reset : resetInput.nreset = 1)
    (pins : Nat → Inputs) (n : Nat) : Invariant (run (step initial resetInput) pins n) := by
  induction n with
  | zero => exact reset_invariant initial resetInput reset
  | succ n ih => exact step_invariant _ _ ih

theorem multiply_latency (s : State) (operation : s.r11_ncontractFn < 4#4) :
    MulDivCheckedLatency.latency s = cycles s := by
  have multiply : s.r11_ncontractFn.extractLsb' 2 1 ≠ 1#1 := by bv_decide
  simp [MulDivCheckedLatency.latency, multiply, cycles]

/-- Both exported timing assertions hold for every monitored multiply cycle,
including all cycles before completion and arbitrary response backpressure. -/
theorem timing_assertions (s : State) (i : Inputs) (invariant : Invariant s)
    (operation : s.r11_ncontractFn < 4#4) :
    ((eval s i).assertions.take 2).all id = true := by
  rw [MulDivCheckedLatency.timing_checks, multiply_latency s operation]
  simp only [Invariant, cycles, offset] at invariant
  simp only [MulDivCheckedLatency.gate, cycles, observe, eval, List.all_cons, List.all_nil, id_eq]
  simp only [← BitVec.le_def]
  bv_decide

theorem timing_assertions_after_reset (initial : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (pins : Nat → Inputs) (n : Nat)
    (operation : (run (step initial resetInput) pins n).r11_ncontractFn < 4#4) :
    ((eval (run (step initial resetInput) pins n) (pins n)).assertions.take 2).all id = true :=
  timing_assertions _ _ (run_invariant initial resetInput reset pins n) operation

end MulDivCheckedMulTiming
