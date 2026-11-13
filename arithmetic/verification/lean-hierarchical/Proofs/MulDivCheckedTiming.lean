import Proofs.MulDivCheckedMonitor

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

/-- The monitor measures computation edges after request acceptance. -/
def expectedAge (s : State) : BitVec 7 := v231 s (recordedRequest s)

theorem expected_age_input_independent (s : State) (i : Inputs) :
    v231 s i = expectedAge s := by rfl

theorem expected_age_bounds (s : State) :
    32 ≤ (expectedAge s).toNat ∧ (expectedAge s).toNat ≤ 67 := by
  simp only [expectedAge, v231, v230, v229, v228, v227, v192, v191, v43, v195]
  split
  · have small (x : BitVec 1) : x = 0#1 ∨ x = 1#1 := by bv_decide
    rcases small (v226 s (recordedRequest s)) with h | h <;>
      rcases small (v225 s (recordedRequest s)) with k | k <;>
      rw [h, k] <;> decide
  · split <;> decide

theorem multiply_expected_age (s : State) (i : Inputs) (multiply : v198 s i = 0) :
    expectedAge s = if s.r12_ncontractDw = 1 then 64#7 else 32#7 := by
  rw [← expected_age_input_independent s i]
  simp only [v231, multiply, v230, v43, v195]
  rfl

theorem division_expected_age (s : State) (i : Inputs) (division : v198 s i = 1) :
    expectedAge s = (0#6 ++ v226 s i) + (0#6 ++ v225 s i) + 65#7 := by
  rw [← expected_age_input_independent s i]
  simp only [v231, division, if_true, v229, v227, v228, v192, v191]

theorem computing_age_no_wrap (s : State) (inputs : Nat → Inputs) (n : Nat)
    (initial : s.r10_ncontractAge = 0) (bound : n ≤ 67)
    (computing : ∀ t, t < n →
      (inputs t).nreset = 0 ∧ v2 (run s inputs t) (inputs t) ≠ 1 ∧
      (run s inputs t).r9_ncontractPending = 1 ∧ v38 (run s inputs t) (inputs t) = 0) :
    (run s inputs n).r10_ncontractAge.toNat = n := by
  rw [age_computing_trace s inputs n initial computing, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (by omega)

end HierarchicalMulDivChecked
