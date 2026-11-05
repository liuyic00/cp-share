import Proofs.ArithmeticBits
namespace NutShellProofs
open nNutCore

def widenedSub (x y : BitVec 64) : BitVec 65 :=
  ((0 : BitVec 1) ++ x) + ((0 : BitVec 1) ++ ~~~y) + 1

theorem widened_sub_carry (x y : BitVec 64) :
    BitVec.extractLsb' 64 1 (widenedSub x y) =
      if x.toNat < y.toNat then (0 : BitVec 1) else 1 := by
  apply BitVec.eq_of_toNat_eq
  have xb := x.isLt
  have yb := y.isLt
  rw [BitVec.extractLsb'_toNat]
  simp only [widenedSub, BitVec.toNat_add]
  rw [BitVec.toNat_append, BitVec.toNat_append]
  simp only [BitVec.toNat_not, BitVec.toNat_ofNat]
  split <;> simp [Nat.shiftRight_eq_div_pow] <;> omega

theorem sign_bit_64 (x : BitVec 64) :
    BitVec.extractLsb' 63 1 x = if 9223372036854775808 ≤ x.toNat then 1 else 0 := by
  apply BitVec.eq_of_toNat_eq
  have bound := x.isLt
  rw [BitVec.extractLsb'_toNat]
  split <;> simp [Nat.shiftRight_eq_div_pow] <;> omega

theorem signed_compare_from_unsigned (x y : BitVec 64) :
    BitVec.extractLsb' 63 1 (x ^^^ y) ^^^
      (if x.toNat < y.toNat then (1 : BitVec 1) else 0) =
      if x.toInt < y.toInt then (1 : BitVec 1) else 0 := by
  have xb := x.isLt
  have yb := y.isLt
  rw [BitVec.extractLsb'_xor, sign_bit_64, sign_bit_64]
  simp only [BitVec.toInt_eq_toNat_cond]
  repeat' first | (split <;> try simp_all) | omega

#print axioms signed_compare_from_unsigned
#print axioms widened_sub_carry
end NutShellProofs
