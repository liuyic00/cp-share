import Proofs.MulDivCheckedTiming
import Proofs.MulDivCheckedDivisionChecks
import Proofs.MulDivCheckedStall
import Proofs.MulDivCheckedDivisionOutput
import Proofs.MulDivCheckedMulOutput

namespace MulDivCheckedAssertions
open nMulDivChecked

/-- Ten of the eleven generated checks hold on every post-reset observation.
Index 3, the response-data assertion, is explicitly excluded here. -/
theorem all_except_response_data_after_reset (initial : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (pins : Nat → Inputs) (n : Nat) :
    (((eval (run (step initial resetInput) pins n) (pins n)).assertions.take 3) ++
      ((eval (run (step initial resetInput) pins n) (pins n)).assertions.drop 4)).all id = true := by
  let s := run (step initial resetInput) pins n
  let i := pins n
  have timing := MulDivCheckedTiming.timing_assertions_after_reset initial resetInput reset pins n
  have tag := MulDivCheckedMetadata.tag_assertion_after_reset initial resetInput reset pins n
  have division := MulDivCheckedDivisionChecks.assertions_after_reset initial resetInput reset pins n
  have stall := MulDivCheckedStall.stall_assertions_trace initial resetInput pins n
  have split : (eval s i).assertions.take 3 ++ (eval s i).assertions.drop 4 =
      ((eval s i).assertions.take 2 ++ [(eval s i).assertions[2]!]) ++
      ((eval s i).assertions.drop 4).take 4 ++ (eval s i).assertions.drop 8 := by rfl
  change ((eval s i).assertions.take 3 ++ (eval s i).assertions.drop 4).all id = true
  rw [split]
  simp only [s, i, List.all_append, List.all_cons, List.all_nil, id_eq, timing, tag, division, stall]
  rfl

theorem response_data_after_reset (initial : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (pins : Nat → Inputs) (n : Nat) :
    (eval (run (step initial resetInput) pins n) (pins n)).assertions[3]! = true := by
  let s := run (step initial resetInput) pins n
  by_cases active : s.r9_ncontractPending = 1 ∧ (observe s (pins n)).nio_5Fresp_5Fvalid = 1
  · have legal := MulDivCheckedMetadata.legal_run initial resetInput reset pins n active.1
    have range : s.r11_ncontractFn < 8#4 := legal.1
    have operations : s.r11_ncontractFn < 4#4 ∨ MulDivCheckedDivisionInit.Operation s := by
      simp only [MulDivCheckedDivisionInit.Operation]
      bv_decide
    rcases operations with multiply | divide
    · exact MulDivCheckedMulOutput.data_assertion_after_reset initial resetInput reset pins n multiply
    · exact MulDivCheckedDivisionOutput.data_assertion_after_reset initial resetInput reset pins n divide
  · exact MulDivCheckedData.inactive s (pins n) active

/-- All eleven source assertions hold at every observation after reset, with
arbitrary later requests, operands, resets, cancellation, and response readiness. -/
theorem all_assertions_after_reset (initial : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (pins : Nat → Inputs) (n : Nat) :
    asserts (run (step initial resetInput) pins n) (pins n) := by
  let s := run (step initial resetInput) pins n
  let i := pins n
  have rest := all_except_response_data_after_reset initial resetInput reset pins n
  have data := response_data_after_reset initial resetInput reset pins n
  simp only [List.all_append, Bool.and_eq_true] at rest
  have split : (eval s i).assertions =
      ((eval s i).assertions.take 3 ++ [(eval s i).assertions[3]!]) ++ (eval s i).assertions.drop 4 := by rfl
  change (eval s i).assertions.all id = true
  rw [split]
  simp only [s, i, List.all_append, List.all_cons, List.all_nil, id_eq, rest.1, rest.2, data]
  rfl

end MulDivCheckedAssertions
