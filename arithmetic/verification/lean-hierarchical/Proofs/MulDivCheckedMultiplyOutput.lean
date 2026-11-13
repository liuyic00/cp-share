import Proofs.MulDivCheckedOutputTrace
import Proofs.MulDivCheckedMultiplyMetadata

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

theorem multiply_output_after_reset (s : State) (resetInput : Inputs) (inputs : Nat → Inputs)
    (reset : resetInput.nreset = 1) (n : Nat)
    (multiply : v198 (run (step s resetInput) inputs n) (inputs n) = 0) :
    v267 (run (step s resetInput) inputs n) (inputs n) ≠ 1 ∨
      v268 (run (step s resetInput) inputs n) (inputs n) = 1 := by
  let current := run (step s resetInput) inputs n
  have value : current.r9_ncontractPending = 1 → v38 current (inputs n) = 1 →
      v187 current (inputs n) = v258 current (inputs n) := by
    intro pending ready
    have legal := legal_after_reset s resetInput reset inputs n pending
    simp only [legalArithmetic, HierarchicalMulDiv.legalArithmetic, coreInputs, recordedRequest] at legal
    have operation : current.r11_ncontractFn = 0#4 ∨
        (current.r12_ncontractDw = 1 ∧
          (current.r11_ncontractFn = 1#4 ∨ current.r11_ncontractFn = 2#4 ∨ current.r11_ncontractFn = 3#4)) := by
      change v198 current (inputs n) = 0 at multiply
      simp only [v198] at multiply
      bv_decide
    have actual := pending_response_arithmetic s resetInput inputs reset n pending ready
    simp only [observe, eval_eq_spec, evalSpec] at actual
    rw [multiplication_monitor_specification current (inputs n) operation]
    have notSigned : ¬(current.r11_ncontractFn = 4#4 ∨ current.r11_ncontractFn = 6#4) := by bv_decide
    have notUnsigned : ¬(current.r11_ncontractFn = 5#4 ∨ current.r11_ncontractFn = 7#4) := by bv_decide
    change v187 current (inputs n) = arithmeticSpecification (recordedRequest current) at actual
    simpa only [arithmeticSpecification, HierarchicalMulDiv.arithmeticSpecification,
      coreInputs, recordedRequest, notSigned, notUnsigned, if_false] using actual
  change v267 current (inputs n) ≠ 1 ∨ v268 current (inputs n) = 1
  simp only [v267, v265, v259, v268]
  bv_decide

end HierarchicalMulDivChecked
