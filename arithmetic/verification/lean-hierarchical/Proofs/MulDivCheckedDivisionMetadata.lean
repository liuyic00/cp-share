import Proofs.MulDivCheckedTiming
import Proofs.MulDivSignedRequest

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

/-- The monitor's normalized operands agree with the operands used by the
    signed division contract, including sign extension in word mode. -/
theorem signed_monitor_operands (s : State) (i : Inputs)
    (operation : s.r11_ncontractFn = 4#4 ∨ s.r11_ncontractFn = 6#4) :
    v206 s i = HierarchicalMulDiv.signedA (coreInputs (recordedRequest s)) ∧
    v212 s i = HierarchicalMulDiv.signedB (coreInputs (recordedRequest s)) := by
  simp only [v206, v205, v204, v203, v202, v201, v200, v199, v31,
    v212, v211, v210, v209, v208, v207,
    HierarchicalMulDiv.signedA, HierarchicalMulDiv.signedB,
    HierarchicalMulDiv.signedOperand, coreInputs, recordedRequest]
  bv_decide

theorem signed_monitor_signs (s : State) (i : Inputs)
    (operation : s.r11_ncontractFn = 4#4 ∨ s.r11_ncontractFn = 6#4) :
    v214 s i = HierarchicalMulDiv.operandSign (HierarchicalMulDiv.signedA (coreInputs (recordedRequest s))) ∧
    v216 s i = HierarchicalMulDiv.operandSign (HierarchicalMulDiv.signedB (coreInputs (recordedRequest s))) := by
  obtain ⟨a, b⟩ := signed_monitor_operands s i operation
  simp only [v214, v216, v213, v215, a, b, HierarchicalMulDiv.operandSign,
    v200, v199, v31]
  bv_decide

theorem signed_monitor_magnitudes (s : State) (i : Inputs)
    (operation : s.r11_ncontractFn = 4#4 ∨ s.r11_ncontractFn = 6#4) :
    v218 s i = HierarchicalMulDiv.absoluteWord (HierarchicalMulDiv.signedA (coreInputs (recordedRequest s))) ∧
    v220 s i = HierarchicalMulDiv.absoluteWord (HierarchicalMulDiv.signedB (coreInputs (recordedRequest s))) := by
  obtain ⟨a, b⟩ := signed_monitor_operands s i operation
  obtain ⟨sa, sb⟩ := signed_monitor_signs s i operation
  simp only [v218, v217, v220, v219, v143, a, b, sa, sb,
    HierarchicalMulDiv.absoluteWord]
  bv_decide

theorem signed_monitor_setup_time (s : State) (i : Inputs)
    (operation : s.r11_ncontractFn = 4#4 ∨ s.r11_ncontractFn = 6#4) :
    HierarchicalMulDiv.signedSetupTime (coreInputs (recordedRequest s)) =
      1 + (v226 s i).toNat := by
  obtain ⟨sa, sb⟩ := signed_monitor_signs s i operation
  unfold HierarchicalMulDiv.signedSetupTime
  rw [v226, sa, sb]
  have bit_cases (x : BitVec 1) : x = 0#1 ∨ x = 1#1 := by bv_decide
  rcases bit_cases (HierarchicalMulDiv.operandSign
      (HierarchicalMulDiv.signedA (coreInputs (recordedRequest s))) |||
      HierarchicalMulDiv.operandSign (HierarchicalMulDiv.signedB (coreInputs (recordedRequest s)))) with h | h <;>
    rw [h] <;> decide

theorem signed_monitor_correction (s : State) (i : Inputs)
    (operation : s.r11_ncontractFn = 4#4 ∨ s.r11_ncontractFn = 6#4) :
    v225 s i =
      if HierarchicalMulDiv.absoluteWord
          (HierarchicalMulDiv.signedB (coreInputs (recordedRequest s))) = 0#64 then
        if HierarchicalMulDiv.signedHigh (coreInputs (recordedRequest s)) = 0#1
          then 0#1 else HierarchicalMulDiv.signedNegative (coreInputs (recordedRequest s))
      else HierarchicalMulDiv.signedNegative (coreInputs (recordedRequest s)) := by
  obtain ⟨sa, sb⟩ := signed_monitor_signs s i operation
  have magnitude := (signed_monitor_magnitudes s i operation).2
  simp only [v225, v224, v223, v222, v221, v143, sa, sb, magnitude,
    HierarchicalMulDiv.signedHigh, HierarchicalMulDiv.signedNegative,
    coreInputs, recordedRequest]
  bv_decide

theorem unsigned_monitor_metadata (s : State) (i : Inputs)
    (operation : s.r11_ncontractFn = 5#4 ∨ s.r11_ncontractFn = 7#4) :
    v218 s i = HierarchicalMulDiv.unsignedOperand s.r13_ncontractA s.r12_ncontractDw ∧
    v220 s i = HierarchicalMulDiv.unsignedOperand s.r14_ncontractB s.r12_ncontractDw ∧
    v226 s i = 0 ∧ v225 s i = 0 := by
  simp only [v218, v217, v220, v219, v214, v216, v213, v215, v206, v205,
    v204, v203, v202, v201, v200, v199, v31, v143, v212, v211, v210, v209,
    v208, v207, v226, v225, v224, v223, v222, v221, HierarchicalMulDiv.unsignedOperand]
  bv_decide

theorem unsigned_monitor_age (s : State) (i : Inputs)
    (operation : s.r11_ncontractFn = 5#4 ∨ s.r11_ncontractFn = 7#4) :
    expectedAge s = 65#7 := by
  have metadata := unsigned_monitor_metadata s i operation
  have division : v198 s i = 1 := by
    simp only [v198]
    bv_decide
  rw [division_expected_age s i division, metadata.2.2.1, metadata.2.2.2]
  rfl

end HierarchicalMulDivChecked
