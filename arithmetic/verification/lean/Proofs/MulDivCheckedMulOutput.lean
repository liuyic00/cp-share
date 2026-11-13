import Proofs.MulDivCheckedMulBridge
import Proofs.MulDivCheckedMulTrace

namespace MulDivCheckedMulOutput
open nMulDivChecked

theorem data_assertion_after_reset (initial : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (pins : Nat → Inputs) (n : Nat)
    (operation : (run (step initial resetInput) pins n).r11_ncontractFn < 4#4) :
    (eval (run (step initial resetInput) pins n) (pins n)).assertions[3]! = true := by
  let s := run (step initial resetInput) pins n
  by_cases active : s.r9_ncontractPending = 1 ∧ (observe s (pins n)).nio_5Fresp_5Fvalid = 1
  · have legal := MulDivCheckedMetadata.legal_run initial resetInput reset pins n active.1
    change s.r11_ncontractFn < 8#4 ∧ (s.r12_ncontractDw = 1 ∨ s.r11_ncontractFn = 0 ∨ 4#4 ≤ s.r11_ncontractFn) at legal
    change s.r11_ncontractFn < 4#4 at operation
    have capturedLegal : MulDivCheckedMulSpec.Legal (MulDivCheckedHistory.captured s) := by
      simp only [MulDivCheckedMulSpec.Legal, MulDivCheckedHistory.captured]
      bv_decide
    have phases := MulDivCheckedMulTiming.run_invariant initial resetInput reset pins n active.1 operation
    have done : s.r0_nstate = 6 := by
      have valid := active.2
      change (s.r0_nstate = 2 ∧ _) ∨ (s.r0_nstate = 6 ∧ _) at phases
      rcases phases with ⟨state, _⟩ | ⟨state, _⟩
      · simp [observe, eval, state] at valid
      · exact state
    have data := (MulDivCheckedMulTrace.run_invariant initial resetInput reset pins n active.1 operation).2 done (pins n)
    apply MulDivCheckedData.of_correct
    rw [MulDivCheckedMulBridge.expected_eq_specification s capturedLegal]
    exact data
  · exact MulDivCheckedData.inactive s (pins n) active

end MulDivCheckedMulOutput
