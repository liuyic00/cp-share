import Proofs.MulDivCheckedDivisionOutput
import Proofs.MulDivCheckedMultiplyMetadata

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

theorem output_after_reset (s : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (inputs : Nat → Inputs) (n : Nat) :
    OutputInvariant (run (step s resetInput) inputs n) := by
  let current := run (step s resetInput) inputs n
  intro i pending ready
  have actual := pending_response_arithmetic s resetInput inputs reset n pending ready
  change v187 current i = arithmeticSpecification (recordedRequest current) at actual
  have legal := legal_after_reset s resetInput reset inputs n pending
  simp only [legalArithmetic, HierarchicalMulDiv.legalArithmetic, coreInputs, recordedRequest] at legal
  have expected : v258 current i = arithmeticSpecification (recordedRequest current) := by
    rcases legal with mul | signed | unsigned
    · rw [multiplication_monitor_specification current i mul]
      have notSigned : ¬(current.r11_ncontractFn = 4#4 ∨ current.r11_ncontractFn = 6#4) := by bv_decide
      have notUnsigned : ¬(current.r11_ncontractFn = 5#4 ∨ current.r11_ncontractFn = 7#4) := by bv_decide
      simp only [arithmeticSpecification, HierarchicalMulDiv.arithmeticSpecification,
        coreInputs, recordedRequest, notSigned, notUnsigned, if_false]
    · change current.r11_ncontractFn = 4#4 ∨ current.r11_ncontractFn = 6#4 at signed
      have operation : divisionRequest (recordedRequest current) := by
        rcases signed with h | h
        · exact Or.inl h
        · exact Or.inr (Or.inr (Or.inl h))
      have magnitudes := pending_response_magnitudes s resetInput inputs reset n pending ready operation
      rw [signed_monitor_specification current i signed magnitudes.1 magnitudes.2]
      simp only [arithmeticSpecification, HierarchicalMulDiv.arithmeticSpecification,
        coreInputs, recordedRequest, signed, if_true]
    · change current.r11_ncontractFn = 5#4 ∨ current.r11_ncontractFn = 7#4 at unsigned
      have operation : divisionRequest (recordedRequest current) := by
        rcases unsigned with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inr h))
      have magnitudes := pending_response_magnitudes s resetInput inputs reset n pending ready operation
      rw [unsigned_monitor_specification current i unsigned magnitudes.1 magnitudes.2]
      have notSigned : ¬(current.r11_ncontractFn = 4#4 ∨ current.r11_ncontractFn = 6#4) := by bv_decide
      simp only [arithmeticSpecification, HierarchicalMulDiv.arithmeticSpecification,
        coreInputs, recordedRequest, notSigned, unsigned, if_false, if_true]
  exact actual.trans expected.symm

/-- All eleven checked-module assertions hold after a reset edge, with no
    restrictions on subsequent inputs, resets, cancellation or backpressure. -/
theorem asserts_after_reset (s : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (inputs : Nat → Inputs) (n : Nat) :
    asserts (run (step s resetInput) inputs n) (inputs n) := by
  apply asserts_of_invariants
  · exact timing_after_reset s resetInput reset inputs n
  · exact tag_after_reset s resetInput reset inputs n
  · exact output_after_reset s resetInput reset inputs n
  · exact magnitude_after_reset s resetInput reset inputs n
  · cases n with
    | zero => exact stall_after_step s resetInput
    | succ n => exact stall_after_step _ _

#print axioms asserts_after_reset
end HierarchicalMulDivChecked
