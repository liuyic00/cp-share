import Proofs.WritebackSelection
namespace NutShellProofs
open nNutCore

theorem low_add (x y : BitVec w) (bound : n ≤ w) :
    BitVec.extractLsb' 0 n (x + y) = BitVec.extractLsb' 0 n x + BitVec.extractLsb' 0 n y := by
  simp only [← BitVec.setWidth_eq_extractLsb' bound]
  exact BitVec.setWidth_add x y bound

theorem low_low (x : BitVec w) (bound : n ≤ m) :
    BitVec.extractLsb' 0 n (BitVec.extractLsb' 0 m x) = BitVec.extractLsb' 0 n x := by
  apply BitVec.eq_of_getLsbD_eq
  intro k
  simp only [BitVec.getLsbD_extractLsb']
  by_cases small : k < n
  · have bound' : k < m := by omega
    simp [small, bound']
  · simp [small]

theorem twos_complement_sub (x y : BitVec 64) :
    x + (y ^^^ BitVec.ofNat 64 18446744073709551615) + BitVec.ofNat 64 1 = x - y := by
  change x + (y ^^^ BitVec.allOnes 64) + 1 = x - y
  rw [BitVec.xor_allOnes]
  simp [BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, BitVec.add_assoc]

theorem low_shiftLeft (x : BitVec w) (amount : Nat) (bound : n ≤ w) :
    BitVec.extractLsb' 0 n (x <<< amount) = (BitVec.extractLsb' 0 n x) <<< amount := by
  simp only [← BitVec.setWidth_eq_extractLsb' bound]
  exact BitVec.setWidth_shiftLeft_of_le bound

end NutShellProofs
