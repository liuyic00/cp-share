import Proofs.ReferenceBranchConditions
namespace NutShellProofs
open nNutCore
theorem reference_branch_beq_alignment (s : State) (i : Inputs)
    (aligned : BitVec.extractLsb' 0 2 (v16457 s i + v16164 s i) = 0) :
    v23358 s i = 1 := by
  have target : v23344 s i = v16457 s i + v16164 s i := by
    simp only [v23344, v23343, v23341, v23342, low_add _ _ (by decide : 64 ≤ 65),
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64), BitVec.extractLsb'_eq_self]
  have low : BitVec.extractLsb' 0 1 (v16457 s i + v16164 s i) = 0 := by
    have h := congrArg (BitVec.extractLsb' 0 1) aligned
    simpa only [low_low _ (by decide : 1 ≤ 2)] using h
  rcases BitVec.eq_zero_or_eq_one (BitVec.extractLsb' 2 1 (v16429 s i)) with c | c
  all_goals simp [v23336, v23337, v23338, v23339, v23340, v23345, v23346, v23347, v23348, v23349, v23350, v23351, v23352, v23353, v23354, v23355, v23356, v23357, v23358, target, aligned, low, c, v110, v24, v9721, v2750]

theorem reference_branch_bne_alignment (s : State) (i : Inputs)
    (aligned : BitVec.extractLsb' 0 2 (v16457 s i + v16164 s i) = 0) :
    v23334 s i = 1 := by
  have target : v23320 s i = v16457 s i + v16164 s i := by
    simp only [v23320, v23319, v23317, v23318, low_add _ _ (by decide : 64 ≤ 65),
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64), BitVec.extractLsb'_eq_self]
  have low : BitVec.extractLsb' 0 1 (v16457 s i + v16164 s i) = 0 := by
    have h := congrArg (BitVec.extractLsb' 0 1) aligned
    simpa only [low_low _ (by decide : 1 ≤ 2)] using h
  rcases BitVec.eq_zero_or_eq_one (BitVec.extractLsb' 2 1 (v16429 s i)) with c | c
  all_goals simp [v23312, v23313, v23314, v23315, v23316, v23321, v23322, v23323, v23324, v23325, v23326, v23327, v23328, v23329, v23330, v23331, v23332, v23333, v23334, target, aligned, low, c, v110, v24, v9721, v2750]

theorem reference_branch_blt_alignment (s : State) (i : Inputs)
    (aligned : BitVec.extractLsb' 0 2 (v16457 s i + v16164 s i) = 0) :
    v23310 s i = 1 := by
  have target : v23296 s i = v16457 s i + v16164 s i := by
    simp only [v23296, v23295, v23293, v23294, low_add _ _ (by decide : 64 ≤ 65),
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64), BitVec.extractLsb'_eq_self]
  have low : BitVec.extractLsb' 0 1 (v16457 s i + v16164 s i) = 0 := by
    have h := congrArg (BitVec.extractLsb' 0 1) aligned
    simpa only [low_low _ (by decide : 1 ≤ 2)] using h
  rcases BitVec.eq_zero_or_eq_one (BitVec.extractLsb' 2 1 (v16429 s i)) with c | c
  all_goals simp [v23288, v23289, v23290, v23291, v23292, v23297, v23298, v23299, v23300, v23301, v23302, v23303, v23304, v23305, v23306, v23307, v23308, v23309, v23310, target, aligned, low, c, v110, v24, v9721, v2750]

theorem reference_branch_bltu_alignment (s : State) (i : Inputs)
    (aligned : BitVec.extractLsb' 0 2 (v16457 s i + v16164 s i) = 0) :
    v23286 s i = 1 := by
  have target : v23272 s i = v16457 s i + v16164 s i := by
    simp only [v23272, v23271, v23269, v23270, low_add _ _ (by decide : 64 ≤ 65),
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64), BitVec.extractLsb'_eq_self]
  have low : BitVec.extractLsb' 0 1 (v16457 s i + v16164 s i) = 0 := by
    have h := congrArg (BitVec.extractLsb' 0 1) aligned
    simpa only [low_low _ (by decide : 1 ≤ 2)] using h
  rcases BitVec.eq_zero_or_eq_one (BitVec.extractLsb' 2 1 (v16429 s i)) with c | c
  all_goals simp [v23264, v23265, v23266, v23267, v23268, v23273, v23274, v23275, v23276, v23277, v23278, v23279, v23280, v23281, v23282, v23283, v23284, v23285, v23286, target, aligned, low, c, v110, v24, v9721, v2750]

theorem reference_branch_bge_alignment (s : State) (i : Inputs)
    (aligned : BitVec.extractLsb' 0 2 (v16457 s i + v16164 s i) = 0) :
    v23262 s i = 1 := by
  have target : v23248 s i = v16457 s i + v16164 s i := by
    simp only [v23248, v23247, v23245, v23246, low_add _ _ (by decide : 64 ≤ 65),
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64), BitVec.extractLsb'_eq_self]
  have low : BitVec.extractLsb' 0 1 (v16457 s i + v16164 s i) = 0 := by
    have h := congrArg (BitVec.extractLsb' 0 1) aligned
    simpa only [low_low _ (by decide : 1 ≤ 2)] using h
  rcases BitVec.eq_zero_or_eq_one (BitVec.extractLsb' 2 1 (v16429 s i)) with c | c
  all_goals simp [v23240, v23241, v23242, v23243, v23244, v23249, v23250, v23251, v23252, v23253, v23254, v23255, v23256, v23257, v23258, v23259, v23260, v23261, v23262, target, aligned, low, c, v110, v24, v9721, v2750]

theorem reference_branch_bgeu_alignment (s : State) (i : Inputs)
    (aligned : BitVec.extractLsb' 0 2 (v16457 s i + v16164 s i) = 0) :
    v23238 s i = 1 := by
  have target : v23224 s i = v16457 s i + v16164 s i := by
    simp only [v23224, v23223, v23221, v23222, low_add _ _ (by decide : 64 ≤ 65),
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64), BitVec.extractLsb'_eq_self]
  have low : BitVec.extractLsb' 0 1 (v16457 s i + v16164 s i) = 0 := by
    have h := congrArg (BitVec.extractLsb' 0 1) aligned
    simpa only [low_low _ (by decide : 1 ≤ 2)] using h
  rcases BitVec.eq_zero_or_eq_one (BitVec.extractLsb' 2 1 (v16429 s i)) with c | c
  all_goals simp [v23216, v23217, v23218, v23219, v23220, v23225, v23226, v23227, v23228, v23229, v23230, v23231, v23232, v23233, v23234, v23235, v23236, v23237, v23238, target, aligned, low, c, v110, v24, v9721, v2750]



def referenceBranchAlignment (operation : BranchOp) (s : State) (i : Inputs) : BitVec 1 :=
  match operation with
  | .beq => v23358 s i
  | .bne => v23334 s i
  | .blt => v23310 s i
  | .bltu => v23286 s i
  | .bge => v23262 s i
  | .bgeu => v23238 s i

theorem reference_branch_alignment (operation : BranchOp) (s : State) (i : Inputs)
    (aligned : BitVec.extractLsb' 0 2 (referenceBranchTarget operation s i) = 0) :
    referenceBranchAlignment operation s i = 1 := by
  rw [reference_branch_target] at aligned
  cases operation with
  | beq => exact reference_branch_beq_alignment s i aligned
  | bne => exact reference_branch_bne_alignment s i aligned
  | blt => exact reference_branch_blt_alignment s i aligned
  | bltu => exact reference_branch_bltu_alignment s i aligned
  | bge => exact reference_branch_bge_alignment s i aligned
  | bgeu => exact reference_branch_bgeu_alignment s i aligned

#print axioms reference_branch_alignment
end NutShellProofs
