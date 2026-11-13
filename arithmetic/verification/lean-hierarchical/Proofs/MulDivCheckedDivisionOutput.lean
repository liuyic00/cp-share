import Proofs.MulDivCheckedMagnitudeInvariant
import Proofs.MulDivCheckedOutputTrace

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

theorem signed_monitor_specification (s : State) (i : Inputs)
    (operation : s.r11_ncontractFn = 4#4 ∨ s.r11_ncontractFn = 6#4)
    (quotient : v232 s i = magnitudeQuotient (divisionMagnitudeA (recordedRequest s))
      (divisionMagnitudeB (recordedRequest s)))
    (residue : v233 s i = magnitudeResidue (divisionMagnitudeA (recordedRequest s))
      (divisionMagnitudeB (recordedRequest s))) :
    v258 s i = HierarchicalMulDiv.signedSpecification (coreInputs (recordedRequest s)) := by
  have division : v198 s i = 1 := by simp only [v198]; bv_decide
  have high : v221 s i = HierarchicalMulDiv.signedHigh (coreInputs (recordedRequest s)) := by
    simp only [v221, HierarchicalMulDiv.signedHigh, coreInputs, recordedRequest]
    bv_decide
  rw [division_monitor_format s i division, quotient, residue, high,
    signed_monitor_correction s i operation]
  simp only [divisionMagnitudeA, divisionMagnitudeB,
    show (recordedRequest s).nio_5Freq_5Fbits_5Ffn = s.r11_ncontractFn from rfl,
    operation, if_true, magnitudeQuotient, magnitudeResidue,
    HierarchicalMulDiv.signedSpecification, HierarchicalMulDiv.normalizedSpecification]
  split <;> rfl

theorem unsigned_monitor_specification (s : State) (i : Inputs)
    (operation : s.r11_ncontractFn = 5#4 ∨ s.r11_ncontractFn = 7#4)
    (quotient : v232 s i = magnitudeQuotient (divisionMagnitudeA (recordedRequest s))
      (divisionMagnitudeB (recordedRequest s)))
    (residue : v233 s i = magnitudeResidue (divisionMagnitudeA (recordedRequest s))
      (divisionMagnitudeB (recordedRequest s))) :
    v258 s i = HierarchicalMulDiv.unsignedSpecification (coreInputs (recordedRequest s)) := by
  have division : v198 s i = 1 := by simp only [v198]; bv_decide
  have notSigned : ¬(s.r11_ncontractFn = 4#4 ∨ s.r11_ncontractFn = 6#4) := by bv_decide
  have high : v221 s i = (if s.r11_ncontractFn = 7#4 then 1#1 else 0#1) := by
    simp only [v221]; bv_decide
  rw [division_monitor_format s i division, quotient, residue, high,
    (unsigned_monitor_metadata s i operation).2.2.2]
  simp only [divisionMagnitudeA, divisionMagnitudeB,
    show (recordedRequest s).nio_5Freq_5Fbits_5Ffn = s.r11_ncontractFn from rfl,
    notSigned, if_false, magnitudeQuotient, magnitudeResidue,
    HierarchicalMulDiv.unsignedSpecification, HierarchicalMulDiv.formatCorrected,
    HierarchicalMulDiv.formatUnsigned, coreInputs, recordedRequest]
  by_cases zero : HierarchicalMulDiv.unsignedOperand s.r14_ncontractB s.r12_ncontractDw = 0#64
  · simp [zero]
  · simp [zero]

end HierarchicalMulDivChecked
