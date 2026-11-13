import Proofs.BoothSelector

namespace HierarchicalBooth

/-- Widen the raw row before adding its correction. This preserves the positive
    endpoint produced by negating twice the minimum signed 65-bit operand. -/
theorem corrected_wide_partial (code : BitVec 3) (b : BitVec 65) :
    (rawPartial code (b.signExtend 66)).signExtend 130 +
      (correction code).setWidth 130 =
    BitVec.ofInt 130 (coefficient code * b.toInt) := by
  rw [BitVec.ofInt_mul]
  change _ = BitVec.ofInt 130 (coefficient code) * b.signExtend 130
  have cases : code = 0 ∨ code = 1 ∨ code = 2 ∨ code = 3 ∨
      code = 4 ∨ code = 5 ∨ code = 6 ∨ code = 7 := by bv_decide
  rcases cases with h | h | h | h | h | h | h | h <;> subst code <;>
    simp [rawPartial, correction, coefficient]
  all_goals first
    | change _ = -(2#130) * b.signExtend 130
      rw [BitVec.neg_mul, BitVec.two_mul]
      bv_decide
    | bv_decide

end HierarchicalBooth
