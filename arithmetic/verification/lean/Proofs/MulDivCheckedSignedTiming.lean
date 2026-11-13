import Proofs.MulDivCheckedLatency

namespace MulDivCheckedSignedTiming
open nMulDivChecked
open MulDivCheckedLatency (operand negative magnitude outputNegative latency)
set_option maxHeartbeats 2000000

def Operation (s : State) : Prop := s.r11_ncontractFn = 4 ∨ s.r11_ncontractFn = 6

def inputExtra (s : State) : BitVec 7 :=
  0#6 ++ (negative s s.r13_ncontractA ||| negative s s.r14_ncontractB)

def rawNegative (s : State) : BitVec 1 :=
  if s.r11_ncontractFn = 6 then negative s s.r13_ncontractA else
    negative s s.r13_ncontractA ^^^ negative s s.r14_ncontractB

def hi (s : State) : BitVec 1 := if s.r11_ncontractFn = 6 then 1 else 0

def Phases (s : State) : Prop :=
  (s.r0_nstate = 1 ∧ s.r10_ncontractAge = 0 ∧ inputExtra s = 1 ∧ s.r3_ncount = 0 ∧
    s.r8_nremainder = 0#66 ++ operand s s.r13_ncontractA ∧
    s.r7_ndivisor = negative s s.r14_ncontractB ++ operand s s.r14_ncontractB ∧
    s.r6_nresHi = 0 ∧ s.r5_nisHi = hi s ∧ s.r4_nneg_5Fout = rawNegative s) ∨
  (s.r0_nstate = 3 ∧ s.r3_ncount = 0 ∧ s.r10_ncontractAge = inputExtra s ∧
    s.r8_nremainder = 0#66 ++ magnitude s s.r13_ncontractA ∧
    s.r7_ndivisor = 0#1 ++ magnitude s s.r14_ncontractB ∧
    s.r5_nisHi = hi s ∧ s.r4_nneg_5Fout = rawNegative s) ∨
  (s.r0_nstate = 3 ∧ 1#7 ≤ s.r3_ncount ∧ s.r3_ncount ≤ 64#7 ∧
    s.r10_ncontractAge = s.r3_ncount + inputExtra s ∧ s.r4_nneg_5Fout = outputNegative s) ∨
  (s.r0_nstate = 5 ∧ s.r10_ncontractAge = 65 + inputExtra s ∧ outputNegative s = 1) ∨
  (s.r0_nstate = 7 ∧ s.r10_ncontractAge = latency s)

def Invariant (s : State) : Prop := s.r9_ncontractPending = 1 → Operation s → Phases s

theorem reset_invariant (s : State) (i : Inputs) (reset : i.nreset = 1) :
    Invariant (step s i) := by
  simp [Invariant, step, eval, reset]

theorem step_invariant (s : State) (i : Inputs) (previous : Invariant s) :
    Invariant (step s i) := by
  intro pending operation
  by_cases idle : s.r0_nstate = 0
  · simp only [Invariant, Operation, Phases, inputExtra, rawNegative, hi, latency, outputNegative,
      magnitude, negative, operand, MulDivCheckedLatency.signedBit, step, eval, idle] at *
    bv_decide
  · have oldPending : s.r9_ncontractPending = 1 := by
      simp only [step, eval] at pending
      bv_decide
    have oldOperation : Operation s := by
      simp only [Operation, step, eval] at operation ⊢
      bv_decide
    have phases := previous oldPending oldOperation
    rcases phases with ⟨state, facts⟩ | ⟨state, facts⟩ | ⟨state, facts⟩ | ⟨state, facts⟩ | ⟨state, facts⟩ <;>
      simp only [Invariant, Operation, Phases, inputExtra, rawNegative, hi, latency, outputNegative,
        magnitude, negative, operand, MulDivCheckedLatency.signedBit, step, eval, state] at * <;>
      bv_decide

theorem run_invariant (initial : State) (resetInput : Inputs) (reset : resetInput.nreset = 1)
    (pins : Nat → Inputs) (n : Nat) : Invariant (run (step initial resetInput) pins n) := by
  induction n with
  | zero => exact reset_invariant initial resetInput reset
  | succ n ih => exact step_invariant _ _ ih

/-- Both exported timing assertions hold throughout signed division, including
input negation, the first iteration's zero-divisor correction, and output negation. -/
theorem timing_assertions (s : State) (i : Inputs) (invariant : Invariant s)
    (operation : Operation s) : ((eval s i).assertions.take 2).all id = true := by
  rw [MulDivCheckedLatency.timing_checks]
  simp only [Invariant, Phases, Operation, inputExtra, rawNegative, hi, latency,
    outputNegative, magnitude, negative, operand, MulDivCheckedLatency.signedBit] at invariant operation ⊢
  simp only [MulDivCheckedLatency.gate, observe, eval, List.all_cons, List.all_nil, id_eq]
  simp only [← BitVec.le_def]
  bv_decide

theorem timing_assertions_after_reset (initial : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (pins : Nat → Inputs) (n : Nat)
    (operation : Operation (run (step initial resetInput) pins n)) :
    ((eval (run (step initial resetInput) pins n) (pins n)).assertions.take 2).all id = true :=
  timing_assertions _ _ (run_invariant initial resetInput reset pins n) operation

end MulDivCheckedSignedTiming
