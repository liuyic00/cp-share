import Std.Tactic

namespace HierarchicalDivision

private theorem zero_append_nat (m n : Nat) (x : BitVec n) :
    ((0#m) ++ x).toNat = x.toNat := by
  rw [BitVec.toNat_append]
  simp

theorem widened_balance (q b r a : BitVec 64)
    (balance : q.toNat * b.toNat + r.toNat = a.toNat) :
    (0#1 ++ ((0#64 ++ q) * (0#64 ++ b))) + (0#65 ++ r) = (0#65 ++ a) := by
  apply BitVec.eq_of_toNat_eq
  have productBound : q.toNat * b.toNat < 2^128 := by
    have := a.isLt
    omega
  have sumBound : q.toNat * b.toNat + r.toNat < 2^129 := by
    have := a.isLt
    omega
  rw [BitVec.toNat_add, zero_append_nat 1 128, zero_append_nat 65 64 r,
    zero_append_nat 65 64 a, BitVec.toNat_mul, zero_append_nat 64 64 q,
    zero_append_nat 64 64 b]
  simp [
    Nat.mod_eq_of_lt productBound, Nat.mod_eq_of_lt sumBound, balance]
  have := a.isLt
  omega

end HierarchicalDivision
