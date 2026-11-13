import Proofs.BoothPadding

namespace BoothRecoding
set_option maxRecDepth 4096
abbrev Row := BitVec 66 × BitVec 2

def correctedSum : List Row → BitVec 130
  | [] => 0#130
  | (p, c) :: rows => (p.signExtend 130 + c.zeroExtend 130) + 4#130 * correctedSum rows

/-- Corrections occur two bit positions below the following row. The last
correction has no following row and is retained separately. -/
def packedTail (previous : BitVec 2) : List Row → BitVec 130
  | [] => previous.zeroExtend 130
  | [(p, c)] => (finalPadded p previous).zeroExtend 130 + 4#130 * c.zeroExtend 130
  | (p, c) :: next :: rows => (middlePadded p previous).zeroExtend 130 +
      4#130 * packedTail c (next :: rows)

def tailOffset : Nat → BitVec 130
  | 0 => 0#130
  | 1 => 295147905179352825856#130
  | n + 2 => 885443715538058477568#130 + 4#130 * tailOffset (n + 1)

private theorem shift_two (p : BitVec 130) : p <<< 2 = 4#130 * p := by bv_decide

theorem packed_tail_eq (rows : List Row) (previous : BitVec 2) :
    packedTail previous rows = previous.zeroExtend 130 + 4#130 * correctedSum rows + tailOffset rows.length := by
  induction rows generalizing previous with
  | nil => simp [packedTail, correctedSum, tailOffset]
  | cons head rows ih =>
    rcases head with ⟨p, c⟩
    cases rows with
    | nil =>
      simp only [packedTail, correctedSum, List.length_cons, List.length_nil, tailOffset,
        final_padding, shift_two, BitVec.mul_add]
      ac_rfl
    | cons next rows =>
      rw [packedTail, ih]
      simp only [correctedSum, List.length_cons, tailOffset, middle_padding,
        shift_two, BitVec.mul_add]
      ac_rfl

/-- The concrete 65-bit array has 33 rows. Its sign padding offsets cancel,
while the delayed corrections retain exactly their original row weights. -/
theorem packed_sum_65 (first : Row) (rows : List Row) (length : rows.length = 32) :
    (firstPadded first.1).zeroExtend 130 + packedTail first.2 rows = correctedSum (first :: rows) := by
  rw [first_padding, packed_tail_eq, length]
  have offsets : 295147905179352825856#130 + tailOffset 32 = 0#130 := by decide
  rw [correctedSum]
  calc
    _ = (first.1.signExtend 130 + first.2.zeroExtend 130 + 4#130 * correctedSum rows) +
      (295147905179352825856#130 + tailOffset 32) := by ac_rfl
    _ = _ := by rw [offsets, BitVec.add_zero]

end BoothRecoding
