import Proofs.MulDivCheckedMultiplyTiming
import Proofs.MulDivCheckedUnsignedTiming

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

theorem timing_checks_of_contract (s : State) (i : Inputs)
    (contract : s.r9_ncontractPending = 1 →
      s.r10_ncontractAge.ule (expectedAge s) = true ∧
      (v38 s i = 1 ↔ s.r10_ncontractAge = expectedAge s)) :
    (v262 s i ≠ 1 ∨ v260 s i = 1) ∧
    (v262 s i ≠ 1 ∨ v264 s i = 1) := by
  have compare : v260 s i =
      (if s.r10_ncontractAge.ule (expectedAge s) then 1#1 else 0#1) := by
    simp only [v260, expected_age_input_independent, BitVec.ule_eq_decide,
      decide_eq_true_eq]
    rfl
  rw [← expected_age_input_independent s i] at contract compare
  simp only [v262, v259, compare, v264, v263]
  bv_decide

theorem multiplication_timing_checks (s : State) (i : Inputs)
    (inv : MultiplyTimingInvariant s) (multiply : v198 s i = 0) :
    (v262 s i ≠ 1 ∨ v260 s i = 1) ∧
    (v262 s i ≠ 1 ∨ v264 s i = 1) :=
  timing_checks_of_contract s i (fun pending => multiply_timing_contract s i inv pending multiply)

theorem unsigned_division_timing_checks (s : State) (i : Inputs)
    (inv : UnsignedTimingInvariant s)
    (operation : s.r11_ncontractFn = 5#4 ∨ s.r11_ncontractFn = 7#4) :
    (v262 s i ≠ 1 ∨ v260 s i = 1) ∧
    (v262 s i ≠ 1 ∨ v264 s i = 1) :=
  timing_checks_of_contract s i (fun pending => unsigned_timing_contract s i inv pending operation)

end HierarchicalMulDivChecked
