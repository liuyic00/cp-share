import Proofs.MemoryExceptionSources
namespace NutShellProofs
open nNutCore
theorem memory_vector_remaining_sources_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (illegal : v13672 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
 :
    v13683 (run initial inputs (t + 1)) (inputs (t + 1)) =
      (if v11638 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 then (64 : BitVec 16) else 0) |||
      (if v11632 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 then (16 : BitVec 16) else 0) := by
  have constants := (memory_constant_exception_run initial inputs reset t).2 valid unit
  rcases constants with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  have page := (memory_page_fault_run initial inputs reset t).2 valid unit
  have access := (memory_access_fault_run initial inputs reset t).2 valid unit
  simp only [v13672] at illegal
  rw [memory_exception_vector_without_csr _ _ unit]
  apply BitVec.eq_of_getLsbD_eq
  intro k
  by_cases bound : k < 16
  · have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 ∨ k = 10 ∨ k = 11 ∨ k = 12 ∨ k = 13 ∨ k = 14 ∨ k = 15 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases BitVec.eq_zero_or_eq_one (v11632 (run initial inputs (t + 1)) (inputs (t + 1))) with loadFault | loadFault <;>
      rcases BitVec.eq_zero_or_eq_one (v11638 (run initial inputs (t + 1)) (inputs (t + 1))) with storeFault | storeFault <;>
      simp [v13638, v13639, v13640, v13641, v13642, v13643, v13644, v13645, v13646, v13647, v13648, v13649, v13650, v13651, v13652, v13653, v13654, v13655, v13656, v13657, v13658, v13659, v13660, v13661, v13662, v13663, v13664, v13665, v13666, v13667, v13668, v13669, v13670, v13671, v13672, v13673, v13674, v13675, v13676, v13677, v13678, v13679, v13680, v13681, v13682, BitVec.getLsbD_append, illegal, loadFault, storeFault, page, access, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]
  · simp [BitVec.getLsbD_of_ge _ _ (by omega : 16 ≤ k)]
#print axioms memory_vector_remaining_sources_run
theorem memory_cause_remaining_sources_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (illegal : v13672 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
 :
    v13780 (run initial inputs (t + 1)) (inputs (t + 1)) =
      if v11638 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 then 6
      else if v11632 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 then 4 else 0 := by
  have vector := memory_vector_remaining_sources_run initial inputs reset t valid unit illegal
  rcases BitVec.eq_zero_or_eq_one (v11632 (run initial inputs (t + 1)) (inputs (t + 1))) with loadFault | loadFault <;>
    rcases BitVec.eq_zero_or_eq_one (v11638 (run initial inputs (t + 1)) (inputs (t + 1))) with storeFault | storeFault <;>
      (unfold v13780 v13745 v13746 v13779 v13747 v8294 v13778 v13748 v13749 v13777 v13750 v13751 v13776 v13752 v13753 v13775 v13754 v8288 v13774 v13755 v8276 v13773 v13756 v8270 v13772 v13757 v13758 v13771 v13759 v13760 v13770 v13761 v15 v13769 v13762 v8300 v13768 v24 v13767 v13763 v11535 v13766 v13764 v9701 v13765
       rw [vector, loadFault, storeFault]
       rfl)
#print axioms memory_cause_remaining_sources_run
end NutShellProofs
