import Proofs.RadixArithmetic

namespace HierarchicalRadix

theorem zero_step (bits : BitVec 129) :
    advance bits 0#64 = (bits <<< 1) + 1#129 := by
  unfold advance
  dsimp only
  rw [if_pos (show (0#64).toNat ≤ (BitVec.extractLsb' 64 65 bits).toNat from Nat.zero_le _)]
  bv_decide

theorem double_ones {w : Nat} (n : Nat) :
    ((BitVec.ofNat w (2 ^ n - 1)) <<< 1) + 1#w =
      BitVec.ofNat w (2 ^ (n + 1) - 1) := by
  rw [BitVec.shiftLeft_eq_mul_twoPow]
  have two : BitVec.twoPow w 1 = BitVec.ofNat w 2 := by
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_twoPow, BitVec.toNat_ofNat]
  rw [two]
  change BitVec.ofNat w (2 ^ n - 1) * BitVec.ofNat w 2 + BitVec.ofNat w 1 = _
  rw [← BitVec.ofNat_mul, ← BitVec.ofNat_add]
  congr 1
  have positive := Nat.two_pow_pos n
  rw [Nat.pow_succ]
  omega

/-- Division by zero shifts in one quotient bit at every edge. -/
theorem zero_iterations (bits : BitVec 129) (n : Nat) :
    advanceMany 0#64 n bits = (bits <<< n) + BitVec.ofNat 129 (2 ^ n - 1) := by
  induction n with
  | zero => simp [advanceMany]
  | succ n ih =>
    rw [advanceMany, zero_step, ih, BitVec.shiftLeft_add_distrib,
      BitVec.add_assoc, double_ones, ← BitVec.shiftLeft_add]

/-- The physical slices implement the specified all-ones quotient and unchanged
    dividend remainder for a zero divisor. -/
theorem zero_result (dividend : BitVec 64) :
    let result := advanceMany 0#64 64 ((0#64 ++ dividend) ++ 0#1)
    BitVec.extractLsb' 0 64 result = BitVec.allOnes 64 ∧
    BitVec.extractLsb' 65 64 result = dividend := by
  dsimp only
  rw [zero_iterations]
  bv_decide

#print axioms zero_result
end HierarchicalRadix
