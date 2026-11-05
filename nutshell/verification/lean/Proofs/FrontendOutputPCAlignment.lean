import Proofs.FrontendAlignedState
import Proofs.OccupiedInstructionPC
namespace NutShellProofs
open nNutCore

/-- Only an unflushed frontend output needs a concrete PC; the generated
invalid-input branch is excluded by redirect gating. -/
theorem frontend_output_pc_aligned (s : State) (i : Inputs)
    (normal : FrontendAlignedState s)
    (head : BitVec.extractLsb' 0 2 (v9733 s i) = 0)
    (noRedirect : v14 s i ≠ BitVec.ofNat 1 1) :
    BitVec.extractLsb' 0 2 (v10174 s i) = 0 := by
  rcases normal with ⟨states, offset⟩
  rcases states with zero | one
  · simpa [v10174, v10167, v9717, v9716, v9715, v18, v17,
      noRedirect, v16, v24, v110, v10173, v9718, v4079, zero] using head
  · simpa [v10174, v10167, v9717, v9716, v9715, v18, v17,
      noRedirect, v16, v24, v110, v10173, v9718, v4079, one,
      v10172, v10090, v10089, v10169,
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 2 ≤ 3)] using offset

/-- A flush may expose arbitrary output PC data, but clears IDU validity.
The relation source is therefore required only without a redirect. -/
theorem idu_instruction_pc_unflushed_step (relation : BitVec 64 → BitVec 39 → Prop)
    (s : State) (i : Inputs) (old : IDUInstructionPC relation s)
    (source : v14 s i ≠ BitVec.ofNat 1 1 → v11102 s i = 1 →
      relation (v11105 s i) (v10174 s i)) :
    IDUInstructionPC relation (step s i) := by
  by_cases redirect : v14 s i = BitVec.ofNat 1 1
  · intro valid
    change v11101 s i = 1 at valid
    simp [v11101, v11100, v11095, v18, v17, redirect, v15, v24] at valid
  · exact idu_instruction_pc_relation_step relation s i old (source redirect)

#print axioms frontend_output_pc_aligned
#print axioms idu_instruction_pc_unflushed_step
end NutShellProofs
