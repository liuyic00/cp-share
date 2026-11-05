import Proofs.FrontendSequentialPC
namespace NutShellProofs
open nNutCore

/-- Alignment follows through the actual prediction/redirect priority mux.
Each target premise is conditional on that target being selected. -/
theorem fetch_target_aligned (s : State) (i : Inputs)
    (redirect : v14 s i = 1 → BitVec.extractLsb' 0 2 (v2709 s i) = 0)
    (crossline : s.g33.r1066_nfrontend_5Fifu_5FcrosslineJumpLatch = 1 →
      BitVec.extractLsb' 0 2 s.g33.r1067_nfrontend_5Fifu_5FcrosslineJumpTarget = 0)
    (sequential : BitVec.extractLsb' 0 2 (v2749 s i) = 0)
    (predicted : v2736 s i = 1 → v2739 s i ≠ 1 →
      BitVec.extractLsb' 0 2 (v2755 s i) = 0) :
    BitVec.extractLsb' 0 2 (v2759 s i) = 0 := by
  unfold v2759 v2758 v2757 v2756
  split
  · exact redirect (by assumption)
  · split
    · exact crossline (by assumption)
    · split
      · split
        · exact sequential
        · exact predicted (by assumption) (by assumption)
      · exact sequential

/-- Reset establishes IFU alignment; otherwise only a selected update matters. -/
theorem fetch_pc_alignment_step (s : State) (i : Inputs)
    (old : BitVec.extractLsb' 0 2 s.g33.r1065_nfrontend_5Fifu_5Fpc = 0)
    (target : v9673 s i = 1 → BitVec.extractLsb' 0 2 (v2759 s i) = 0) :
    BitVec.extractLsb' 0 2 (step s i).g33.r1065_nfrontend_5Fifu_5Fpc = 0 := by
  change BitVec.extractLsb' 0 2 (v9675 s i) = 0
  unfold v9675 v9674
  split
  · unfold v9671
    decide
  · split
    · exact target (by assumption)
    · exact old
#print axioms fetch_target_aligned
#print axioms fetch_pc_alignment_step
end NutShellProofs
