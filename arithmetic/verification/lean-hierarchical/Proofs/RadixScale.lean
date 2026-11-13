import Proofs.RadixRequest

namespace HierarchicalRadix

/-- The 128-bit loader cannot overflow: it shifts a 65-bit value by at most
    63 places. The remaining compute edges account for the complementary shift. -/
theorem scaled_load (a : BitVec 65) (skip : BitVec 6) :
    2 ^ (64 - skip.toNat) *
      (0#1 ++ ((0#63 ++ a) <<< skip.toNat)).toNat = a.toNat * 18446744073709551616 := by
  have count : skip.toNat ≤ 63 := by have := skip.isLt; omega
  have power : 2 ^ skip.toNat ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) count
  have positive : 0 < 2 ^ skip.toNat := Nat.two_pow_pos _
  have fits : a.toNat * 2 ^ skip.toNat < 2 ^ 128 := by
    calc
      a.toNat * 2 ^ skip.toNat < 2 ^ 65 * 2 ^ skip.toNat :=
        Nat.mul_lt_mul_of_pos_right a.isLt positive
      _ ≤ 2 ^ 65 * 2 ^ 63 := Nat.mul_le_mul_left _ power
      _ = 2 ^ 128 := by decide
  have outer (v : BitVec 128) : (0#1 ++ v).toNat = v.toNat := by
    rw [BitVec.toNat_append]
    simp
  have inner : (0#63 ++ a).toNat = a.toNat := by
    rw [BitVec.toNat_append]
    simp
  rw [outer, BitVec.toNat_shiftLeft, inner, Nat.shiftLeft_eq, Nat.mod_eq_of_lt fits]
  rw [Nat.mul_left_comm, ← Nat.pow_add]
  have sum : 64 - skip.toNat + skip.toNat = 64 := by omega
  rw [sum]

#print axioms scaled_load
end HierarchicalRadix
