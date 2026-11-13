import Proofs.BoothPadding

namespace BoothRecoding

/-- Widen before adding the correction. In particular, recoding -2 times the
minimum 65-bit signed multiplicand must retain the positive 2^65 endpoint. -/
theorem corrected_row_wide (b : BitVec 65) (previous even odd : Bool) :
    let window := BitVec.ofBool odd ++ BitVec.ofBool even ++ BitVec.ofBool previous
    (row (b.signExtend 66) window).signExtend 130 + (correction window).zeroExtend 130 =
      b.signExtend 130 * BitVec.ofInt 130 (digit previous (even, odd)) := by
  cases previous <;> cases even <;> cases odd <;>
    simp [row, correction, digit, bit]
  all_goals try simp only [show 1361129467683753853853498429727072845822#130 = -(2#130) from by decide,
    show 1361129467683753853853498429727072845823#130 = -(1#130) from by decide]
  all_goals try rw [BitVec.mul_neg, BitVec.mul_one]
  all_goals try rw [BitVec.mul_neg, BitVec.mul_two]
  all_goals try rw [BitVec.mul_two]
  all_goals bv_decide

theorem corrected_row_wide_window (b : BitVec 65) (window : BitVec 3) :
    (row (b.signExtend 66) window).signExtend 130 + (correction window).zeroExtend 130 =
      b.signExtend 130 * BitVec.ofInt 130
        (digit (window.getLsbD 0) (window.getLsbD 1, window.getLsbD 2)) := by
  have reconstructed : BitVec.ofBool (window.getLsbD 2) ++ BitVec.ofBool (window.getLsbD 1) ++
      BitVec.ofBool (window.getLsbD 0) = window := by bv_decide
  have result := corrected_row_wide b (window.getLsbD 0) (window.getLsbD 1) (window.getLsbD 2)
  simpa only [reconstructed] using result

end BoothRecoding
