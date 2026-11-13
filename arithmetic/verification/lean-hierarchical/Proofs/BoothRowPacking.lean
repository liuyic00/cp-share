import Std.Tactic

namespace HierarchicalBooth

/-- The initial row replaces sign extension by a fixed bias. -/
theorem first_row (raw : BitVec 66) :
    ((~~~(raw.extractLsb' 65 1) ++ raw.extractLsb' 65 1 ++
      raw.extractLsb' 65 1 ++ raw).setWidth 130) =
    raw.signExtend 130 + BitVec.ofNat 130 (2^68) := by
  bv_decide

/-- Interior rows place the preceding correction below the signed partial
    product and encode sign extension with two bias bits. -/
theorem middle_row (raw : BitVec 66) (previous : BitVec 2) :
    ((1#1 ++ ~~~(raw.extractLsb' 65 1) ++ raw ++ previous).setWidth 130) =
    (raw.signExtend 130 <<< 2) + previous.setWidth 130 +
      BitVec.ofNat 130 (3 * 2^68) := by
  bv_decide

/-- The last row omits the leading interior-row bias bit. -/
theorem last_row (raw : BitVec 66) (previous : BitVec 2) :
    ((~~~(raw.extractLsb' 65 1) ++ raw ++ previous).setWidth 130) =
    (raw.signExtend 130 <<< 2) + previous.setWidth 130 +
      BitVec.ofNat 130 (2^68) := by
  bv_decide

end HierarchicalBooth
