import Proofs.FrontendPCHold
import Proofs.ArithmeticBits
namespace NutShellProofs
open nNutCore

/-- Actual sequential fetch address advances by two or four according to address bit 1. -/
theorem frontend_sequential_address (s : State) (i : Inputs) :
    v2749 s i = s.g33.r1065_nfrontend_5Fifu_5Fpc +
      (if BitVec.extractLsb' 1 1 s.g33.r1065_nfrontend_5Fifu_5Fpc = 1 then 2 else 4) := by
  simp [v2749, v2740, v2744, v2743, v2741, v2742, v2748, v2747, v2745, v2746,
    low_add _ _ (by decide : 39 ≤ 40),
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 39 ≤ 39)]
  split <;> rfl

/-- Accepted fetch selects the sequential address when prediction does not redirect it. -/
theorem frontend_sequential_fetch (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (noRedirect : v14 s i = 0)
    (fetch : v9672 s i = 1)
    (noCrossline : s.g33.r1066_nfrontend_5Fifu_5FcrosslineJumpLatch = 0)
    (sequential : v2736 s i = 0 ∨ v2739 s i = 1) :
    (step s i).g33.r1065_nfrontend_5Fifu_5Fpc =
      s.g33.r1065_nfrontend_5Fifu_5Fpc +
        (if BitVec.extractLsb' 1 1 s.g33.r1065_nfrontend_5Fifu_5Fpc = 1 then 2 else 4) := by
  change v9675 s i = _
  rcases sequential with absent | notTaken
  · simp [v9675, v1, v0, reset, v9674, v9673, noRedirect, fetch,
      v2759, v2758, noCrossline, v2757, absent, frontend_sequential_address]
  · rcases BitVec.eq_zero_or_eq_one (v2736 s i) with h | h <;>
      simp [v9675, v1, v0, reset, v9674, v9673, noRedirect, fetch,
        v2759, v2758, noCrossline, v2757, h, v2756, notTaken, frontend_sequential_address]


theorem frontend_word_aligned_sequential_fetch (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (noRedirect : v14 s i = 0)
    (fetch : v9672 s i = 1)
    (noCrossline : s.g33.r1066_nfrontend_5Fifu_5FcrosslineJumpLatch = 0)
    (sequential : v2736 s i = 0 ∨ v2739 s i = 1)
    (bit1 : BitVec.extractLsb' 1 1 s.g33.r1065_nfrontend_5Fifu_5Fpc = 0) :
    (step s i).g33.r1065_nfrontend_5Fifu_5Fpc = s.g33.r1065_nfrontend_5Fifu_5Fpc + 4 := by
  simpa [bit1] using frontend_sequential_fetch s i reset noRedirect fetch noCrossline sequential

#print axioms frontend_word_aligned_sequential_fetch
#print axioms frontend_sequential_address
#print axioms frontend_sequential_fetch
end NutShellProofs
