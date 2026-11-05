import Proofs.StoreDataSemantics
namespace RiscvMiniProofs

private theorem two_bit_cases (x : BitVec 2) : x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by
  have bound := x.isLt
  have cases : x.toNat = 0 ∨ x.toNat = 1 ∨ x.toNat = 2 ∨ x.toNat = 3 := by omega
  rcases cases with h | h | h | h
  · exact Or.inl (BitVec.eq_of_toNat_eq h)
  · exact Or.inr (Or.inl (BitVec.eq_of_toNat_eq h))
  · exact Or.inr (Or.inr (Or.inl (BitVec.eq_of_toNat_eq h)))
  · exact Or.inr (Or.inr (Or.inr (BitVec.eq_of_toNat_eq h)))

theorem store_byte_roundtrip (address source : BitVec 32) :
    checkedStoreData (storeMask 3 address source) address (storeData 3 address source) =
      (0#24) ++ (BitVec.extractLsb' 0 8 source) := by
  rcases two_bit_cases (BitVec.extractLsb' 0 2 address) with h | h | h | h
  · exact store_sb_offset_0 address source h
  · exact store_sb_offset_1 address source h
  · exact store_sb_offset_2 address source h
  · exact store_sb_offset_3 address source h

theorem store_half_roundtrip (address source : BitVec 32)
    (aligned : BitVec.extractLsb' 0 1 address = 0) :
    checkedStoreData (storeMask 2 address source) address (storeData 2 address source) =
      (0#16) ++ (BitVec.extractLsb' 0 16 source) := by
  rcases two_bit_cases (BitVec.extractLsb' 0 2 address) with h | h | h | h
  · exact store_sh_offset_0 address source h
  · have bad : BitVec.extractLsb' 0 1 address = 1 := by
      rw [← extract_prefix address 2 0 1 (by decide), h]
      rfl
    rw [aligned] at bad
    contradiction
  · exact store_sh_offset_2 address source h
  · have bad : BitVec.extractLsb' 0 1 address = 1 := by
      rw [← extract_prefix address 2 0 1 (by decide), h]
      rfl
    rw [aligned] at bad
    contradiction

theorem store_word_roundtrip (address source : BitVec 32)
    (aligned : BitVec.extractLsb' 0 2 address = 0) :
    checkedStoreData (storeMask 1 address source) address (storeData 1 address source) = source :=
  store_sw_offset_0 address source aligned

#print axioms store_byte_roundtrip
#print axioms store_half_roundtrip
#print axioms store_word_roundtrip
end RiscvMiniProofs
