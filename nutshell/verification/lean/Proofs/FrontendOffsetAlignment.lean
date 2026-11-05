import Proofs.FrontendAssertion
import Proofs.ArithmeticBits
namespace NutShellProofs
open nNutCore

/-- The buffer selects either the queued PC offset or its retained offset. -/
theorem frontend_selected_offset_aligned (s : State) (i : Inputs)
    (queued : BitVec.extractLsb' 0 2 (v9733 s i) = 0)
    (retained : BitVec.extractLsb' 0 2 s.g33.r1074_nfrontend_5Fibf_5FpcOffsetR = 0) :
    BitVec.extractLsb' 0 2 (v9735 s i) = 0 := by
  unfold v9735
  split
  · simpa [v9734, low_low _ (by decide : 2 ≤ 3)] using queued
  · exact retained

/-- Advancing past a non-compressed instruction preserves offset alignment. -/
theorem frontend_offset_advance_aligned (s : State) (i : Inputs)
    (aligned : BitVec.extractLsb' 0 2 (v9735 s i) = 0)
    (fullWidth : v9780 s i = 0) :
    BitVec.extractLsb' 0 2 (v10146 s i) = 0 ∧
    BitVec.extractLsb' 0 2 (v10153 s i) = 0 := by
  constructor <;>
    simp [v10146, v10153, v10145, v10152, v10141, v10148,
      v10144, v10151, v10143, v10150, fullWidth, v4, v24,
      low_low _ (by decide : 2 ≤ 3), low_add _ _ (by decide : 2 ≤ 4),
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 2 ≤ 3), aligned]

/-- The normal offset-update paths preserve alignment; the special halfword
restart must be ruled out separately by the reachable buffer-state invariant. -/
theorem frontend_offset_step_aligned (s : State) (i : Inputs)
    (retained : BitVec.extractLsb' 0 2 s.g33.r1074_nfrontend_5Fibf_5FpcOffsetR = 0)
    (selected : BitVec.extractLsb' 0 2 (v9735 s i) = 0)
    (fullWidth : v9780 s i = 0)
    (normalState : v10092 s i = 0) :
    BitVec.extractLsb' 0 2 (step s i).g33.r1074_nfrontend_5Fibf_5FpcOffsetR = 0 := by
  have advance := frontend_offset_advance_aligned s i selected fullWidth
  change BitVec.extractLsb' 0 2 (v10161 s i) = 0
  simp only [v10161, v10160, v10159, v10158, v10157, v10156,
    v10154, v10147, normalState]
  simp only [show (0 : BitVec 1) ≠ 1 by decide, ↓reduceIte]
  repeat' split
  all_goals first | exact retained | exact advance.1 | exact advance.2 | rfl
#print axioms frontend_selected_offset_aligned
#print axioms frontend_offset_advance_aligned
#print axioms frontend_offset_step_aligned
end NutShellProofs
