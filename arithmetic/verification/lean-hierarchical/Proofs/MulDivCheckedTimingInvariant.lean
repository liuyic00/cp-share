import Proofs.MulDivCheckedAssertions
import Proofs.MulDivCheckedSignedTiming

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

theorem timing_after_reset (s : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (inputs : Nat → Inputs) (n : Nat) :
    TimingInvariant (run (step s resetInput) inputs n) := by
  let current := run (step s resetInput) inputs n
  have legal := legal_after_reset s resetInput reset inputs n
  have multiply := multiply_timing_after_reset s resetInput reset inputs n
  have unsigned := unsigned_timing_after_reset s resetInput reset inputs n
  have signed := signed_timing_after_reset s resetInput reset inputs n
  intro i pending
  have operation := legal pending
  change HierarchicalMulDiv.legalArithmetic (coreInputs (recordedRequest current)) at operation
  simp only [HierarchicalMulDiv.legalArithmetic, coreInputs, recordedRequest] at operation
  rcases operation with mul | sign | unsign
  · have division : v198 current i = 0 := by simp only [v198]; bv_decide
    exact multiply_timing_contract current i multiply pending division
  · exact signed_timing_contract current i signed pending sign
  · exact unsigned_timing_contract current i unsigned pending unsign

theorem timing_checks_after_reset (s : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (inputs : Nat → Inputs) (n : Nat) :
    let current := run (step s resetInput) inputs n
    (v262 current (inputs n) ≠ 1 ∨ v260 current (inputs n) = 1) ∧
    (v262 current (inputs n) ≠ 1 ∨ v264 current (inputs n) = 1) :=
  timing_checks_of_contract _ _ (timing_after_reset s resetInput reset inputs n (inputs n))

end HierarchicalMulDivChecked
