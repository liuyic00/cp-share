import Std.Tactic

namespace CarrySaveWide

theorem half_adder (a b : BitVec 130) :
    (a ^^^ b) + ((a &&& b) <<< 1) = a + b := by
  bv_decide

theorem full_adder (a b c : BitVec 130) :
    (a ^^^ b ^^^ c) + (((a &&& b) ||| ((a ^^^ b) &&& c)) <<< 1) = a + b + c := by
  bv_decide

end CarrySaveWide
