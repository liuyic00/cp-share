import Proofs.MulDivResponse
import Proofs.RadixZeroArithmetic

namespace HierarchicalMulDiv

def zeroBits (a : BitVec 64) (n : Nat) : BitVec 130 :=
  ((0#66 ++ a) <<< n) + BitVec.ofNat 130 (2 ^ n - 1)

theorem zeroBits_bound (a : BitVec 64) (n : Nat) (range : n ≤ 64) :
    (zeroBits a n).toNat < 2 ^ 128 := by
  have power := Nat.pow_le_pow_right (by decide : 0 < 2) range
  have positive := Nat.two_pow_pos n
  have width : a.toNat + 1 ≤ 2 ^ 64 := by have := a.isLt; omega
  have product : (a.toNat + 1) * 2 ^ n ≤ 2 ^ 128 := by
    calc
      (a.toNat + 1) * 2 ^ n ≤ 2 ^ 64 * 2 ^ n := Nat.mul_le_mul_right _ width
      _ ≤ 2 ^ 64 * 2 ^ 64 := Nat.mul_le_mul_left _ power
      _ = 2 ^ 128 := by decide
  rw [Nat.add_mul, Nat.one_mul] at product
  have append : (0#66 ++ a).toNat = a.toNat := by
    rw [HierarchicalRadix.append_value]
    simp
  unfold zeroBits
  rw [BitVec.toNat_add, BitVec.toNat_shiftLeft, append, Nat.shiftLeft_eq, BitVec.toNat_ofNat]
  have first := Nat.mod_le (a.toNat * 2 ^ n) (2 ^ 130)
  have second := Nat.mod_le (2 ^ n - 1) (2 ^ 130)
  have total := Nat.mod_le ((a.toNat * 2 ^ n) % 2 ^ 130 + (2 ^ n - 1) % 2 ^ 130) (2 ^ 130)
  omega

theorem zeroBits_step (a : BitVec 64) (n : Nat) (range : n ≤ 64) :
    divisionAdvance (zeroBits a n) 0#65 = zeroBits a (n + 1) := by
  have bound := zeroBits_bound a n range
  have high : BitVec.extractLsb' 128 2 (zeroBits a n) = 0#2 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_ofNat]
    omega
  have digit (bits : BitVec 130) (upper : BitVec.extractLsb' 128 2 bits = 0#2) :
      divisionAdvance bits 0#65 = (bits <<< 1) + 1#130 := by
    unfold divisionAdvance
    bv_decide
  rw [digit _ high]
  unfold zeroBits
  rw [BitVec.shiftLeft_add_distrib, BitVec.add_assoc, HierarchicalRadix.double_ones,
    ← BitVec.shiftLeft_add]

theorem zeroBits_result (a : BitVec 64) :
    BitVec.extractLsb' 0 64 (zeroBits a 65) = BitVec.allOnes 64 ∧
    BitVec.extractLsb' 65 64 (zeroBits a 65) = a := by
  unfold zeroBits
  bv_decide

#print axioms zeroBits_step
#print axioms zeroBits_result
end HierarchicalMulDiv
