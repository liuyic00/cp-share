import Std.Tactic

namespace BitPacking

theorem append_nat (a : BitVec m) (b : BitVec n) :
    (a ++ b).toNat = a.toNat * 2^n + b.toNat := by
  rw [BitVec.toNat_append, ← Nat.shiftLeft_add_eq_or_of_lt b.isLt, Nat.shiftLeft_eq]

theorem three_step (weight a b c x y z total : Nat)
    (previous : total = a + b + c) :
    total + weight * (x + y + z) =
      (x * weight + a) + (y * weight + b) + (z * weight + c) := by
  rw [previous, Nat.mul_add, Nat.mul_add]
  ac_rfl

end BitPacking
