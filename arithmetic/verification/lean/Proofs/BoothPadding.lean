import Proofs.BoothRecoding

namespace BoothRecoding

/-- The actual first-row sign padding contributes a fixed offset. -/
def firstPadded (p : BitVec 66) : BitVec 69 :=
  let s := p.extractLsb' 65 1
  ((~~~s ++ s) ++ s) ++ p

def middlePadded (p : BitVec 66) (correction : BitVec 2) : BitVec 70 :=
  (1#1 ++ (~~~(p.extractLsb' 65 1) ++ p)) ++ correction

def finalPadded (p : BitVec 66) (correction : BitVec 2) : BitVec 69 :=
  (~~~(p.extractLsb' 65 1) ++ p) ++ correction

theorem first_padding (p : BitVec 66) :
    (firstPadded p).zeroExtend 130 = p.signExtend 130 + 295147905179352825856#130 := by
  simp only [firstPadded]
  bv_decide

theorem middle_padding (p : BitVec 66) (correction : BitVec 2) :
    (middlePadded p correction).zeroExtend 130 =
      (p.signExtend 130 <<< 2) + correction.zeroExtend 130 + 885443715538058477568#130 := by
  simp only [middlePadded]
  bv_decide

theorem final_padding (p : BitVec 66) (correction : BitVec 2) :
    (finalPadded p correction).zeroExtend 130 =
      (p.signExtend 130 <<< 2) + correction.zeroExtend 130 + 295147905179352825856#130 := by
  simp only [finalPadded]
  bv_decide

/-- Offset of the first row and n middle rows, before the final row. -/
def paddingOffsets : Nat → Nat
  | 0 => 2^68
  | n + 1 => paddingOffsets n + 3 * 2^68 * 4^n

theorem padding_offsets (n : Nat) : paddingOffsets n = 2^68 * 4^n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [paddingOffsets, ih, Nat.pow_succ]
    omega

/-- For 65-bit operands, all fixed sign-padding offsets vanish modulo
130 bits: the first 31 middle rows contribute 2^130 and the last another 2^130. -/
theorem padding_offsets_65 :
    BitVec.ofNat 130 (paddingOffsets 31 + 2^68 * 2^62) = 0 := by
  rw [padding_offsets]
  decide

end BoothRecoding
