import Proofs.MulDivCheckedMagnitudeReachability
import Proofs.MulDivCheckedDivisionMetadata

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

theorem division_request_of_legal (s : State) (i : Inputs)
    (legal : legalArithmetic (recordedRequest s)) (division : v198 s i = 1) :
    divisionRequest (recordedRequest s) := by
  simp only [legalArithmetic, HierarchicalMulDiv.legalArithmetic, coreInputs,
    recordedRequest] at legal
  simp only [divisionRequest, recordedRequest, v198] at *
  bv_decide

theorem monitor_magnitude_operands (s : State) (i : Inputs)
    (operation : divisionRequest (recordedRequest s)) :
    v218 s i = divisionMagnitudeA (recordedRequest s) ∧
    v220 s i = divisionMagnitudeB (recordedRequest s) := by
  by_cases signed : s.r11_ncontractFn = 4#4 ∨ s.r11_ncontractFn = 6#4
  · simpa only [divisionMagnitudeA, divisionMagnitudeB,
      show (recordedRequest s).nio_5Freq_5Fbits_5Ffn = s.r11_ncontractFn from rfl,
      signed, if_true] using signed_monitor_magnitudes s i signed
  · have unsigned : s.r11_ncontractFn = 5#4 ∨ s.r11_ncontractFn = 7#4 := by
      change s.r11_ncontractFn = 4#4 ∨ s.r11_ncontractFn = 5#4 ∨
        s.r11_ncontractFn = 6#4 ∨ s.r11_ncontractFn = 7#4 at operation
      rcases operation with h | h | h | h
      · exact (signed (Or.inl h)).elim
      · exact Or.inl h
      · exact (signed (Or.inr h)).elim
      · exact Or.inr h
    have operands := unsigned_monitor_metadata s i unsigned
    simpa only [divisionMagnitudeA, divisionMagnitudeB,
      show (recordedRequest s).nio_5Freq_5Fbits_5Ffn = s.r11_ncontractFn from rfl,
      signed, if_false] using And.intro operands.1 operands.2.1

theorem magnitude_after_reset (s : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (inputs : Nat → Inputs) (n : Nat) :
    MagnitudeInvariant (run (step s resetInput) inputs n) := by
  let current := run (step s resetInput) inputs n
  intro i pending ready division
  have legal := legal_after_reset s resetInput reset inputs n pending
  have operation := division_request_of_legal current i legal division
  have result := pending_response_magnitudes s resetInput inputs reset n pending ready operation
  have operands := monitor_magnitude_operands current i operation
  change v232 current i = _ ∧ v233 current i = _ at result
  rw [← operands.1, ← operands.2] at result
  refine ⟨?_, ?_⟩
  · intro zero
    change v220 current i = 0#64 at zero
    simpa [magnitudeQuotient, magnitudeResidue, zero] using result
  · intro nonzero
    rw [result.1, result.2]
    exact magnitude_balance _ _ nonzero

theorem magnitude_checks_after_reset (s : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (inputs : Nat → Inputs) (n : Nat) :
    let current := run (step s resetInput) inputs n
    (v273 current (inputs n) ≠ 1 ∨ v272 current (inputs n) = 1) ∧
    (v273 current (inputs n) ≠ 1 ∨ v274 current (inputs n) = 1) ∧
    (v283 current (inputs n) ≠ 1 ∨ v282 current (inputs n) = 1) ∧
    (v283 current (inputs n) ≠ 1 ∨ v284 current (inputs n) = 1) :=
  magnitude_checks _ _ (magnitude_after_reset s resetInput reset inputs n)

#print axioms magnitude_checks_after_reset
end HierarchicalMulDivChecked
