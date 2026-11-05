import Proofs.Contract

namespace RiscvMiniProofs
open nCoreSoc

-- The forwarded DUT result for x0 remains zero, even on a write to rd=0.
theorem dut_result_x0 (s : State) (i : Inputs) : v9279 s i = 0 := by
  by_cases h : v702 s i = 0
  · simp [v9279, v9278, v9277, v704, v703, v150, h, v9276]
  · simp only [v9279, v9278, v9277, v9275, v9273, v9272, v9274, v9276]
    split <;> (try split) <;> simp_all

-- Exactly assertion index 8 in the unchanged generated list.
-- No reachability or reset hypothesis is needed for this task.
theorem zero_register_task (s : State) (i : Inputs) :
    TaskHolds ⟨8, by decide⟩ s i := by
  change decide (v9283 s i ≠ 1 ∨ v9281 s i = 1) = true
  apply decide_eq_true
  by_cases h : v962 s i = 1
  · right
    simp [v9281, dut_result_x0, v9280, v968, v967, v964, v963, h, v965]
  · left
    simp only [v9283]
    have hz : v962 s i = 0 := by
      apply BitVec.eq_of_toNat_eq
      have hlt := (v962 s i).isLt
      have hn : (v962 s i).toNat ≠ 1 := by
        intro he
        exact h (BitVec.eq_of_toNat_eq he)
      change (v962 s i).toNat = 0
      omega
    simp [hz]

#print axioms zero_register_task
end RiscvMiniProofs
