import Proofs.ScoreboardZero
namespace NutShellProofs
open nNutCore

def registerMask (addr : BitVec 5) : BitVec 32 :=
  BitVec.extractLsb' 0 32 (BitVec.shiftLeft (BitVec.ofNat 63 1)
    (((0 : BitVec 58) ++ addr).toNat))

theorem register_mask_hit (addr : BitVec 5) :
    (registerMask addr).getLsbD addr.toNat = true := by
  have bound := addr.isLt
  have cast : ((0 : BitVec 58) ++ addr).toNat = addr.toNat := by
    rw [BitVec.toNat_append]
    simp
  unfold registerMask
  rw [cast, BitVec.getLsbD_extractLsb', BitVec.shiftLeft_eq, BitVec.getLsbD_shiftLeft]
  simp [
    show addr.toNat < 32 by exact bound, show addr.toNat < 63 by omega]

theorem register_mask_miss (addr index : BitVec 5) (different : addr ≠ index) :
    (registerMask addr).getLsbD index.toNat = false := by
  have bound := index.isLt
  have ne : addr.toNat ≠ index.toNat := fun h => different (BitVec.eq_of_toNat_eq h)
  have cast : ((0 : BitVec 58) ++ addr).toNat = addr.toNat := by
    rw [BitVec.toNat_append]
    simp
  unfold registerMask
  rw [cast, BitVec.getLsbD_extractLsb', BitVec.shiftLeft_eq, BitVec.getLsbD_shiftLeft]
  simp [
    show index.toNat < 32 by exact bound, show index.toNat < 63 by omega]
  omega

theorem clear_zero_preserves_bit (bits : BitVec 32) (addr : BitVec 5)
    (nonzero : addr ≠ 0) :
    ((BitVec.extractLsb' 1 31 bits) ++ (0 : BitVec 1)).getLsbD addr.toNat =
      bits.getLsbD addr.toNat := by
  have bound := addr.isLt
  have positive : 0 < addr.toNat := by
    by_cases h : addr.toNat = 0
    · have eq : addr = 0 := BitVec.eq_of_toNat_eq h
      exact False.elim (nonzero eq)
    · omega
  rw [BitVec.getLsbD_append, if_neg (by omega)]
  simp only [BitVec.getLsbD_extractLsb']
  have lt : addr.toNat - 1 < 31 := by omega
  have eq : 1 + (addr.toNat - 1) = addr.toNat := by omega
  simp [lt, eq]

#print axioms register_mask_hit
#print axioms register_mask_miss
#print axioms clear_zero_preserves_bit
end NutShellProofs
