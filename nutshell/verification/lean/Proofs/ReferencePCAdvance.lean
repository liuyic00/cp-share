import Proofs.ReferenceBranchRedirect
namespace NutShellProofs
open nNutCore

/-- Outer sequential-advance gate, with exception status left explicit. -/
theorem reference_pc_advance_gate (s : State) (i : Inputs)
    (commit : v9 s i = 1) (noException : v23407 s i = 0) :
    v23559 s i = if v23529 s i = 0 then 1 else 0 := by
  simp only [v23559, v23558, v14560, v14559, v14558, commit,
    v23557, noException, v24, ↓reduceIte]
  rfl

theorem reference_pc_plus_four (s : State) (i : Inputs) :
    v23563 s i = v16457 s i + 4 := by
  simp only [v23563, v23562, v23560, v23561, low_add _ _ (by decide : 64 ≤ 65),
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64), BitVec.extractLsb'_eq_self]
  rfl

#print axioms reference_pc_advance_gate
#print axioms reference_pc_plus_four
end NutShellProofs
