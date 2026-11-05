import Proofs.LoadDataCone
namespace RiscvMiniProofs

theorem load_shift_amount (kind : BitVec 3) (address response : BitVec 32) :
    loadData_v732 kind address response = loadData_v2111 0 address response := by
  have bit0 := (extract_prefix address 2 0 1 (by decide)).symm
  have bit1 := (extract_prefix address 2 1 1 (by decide)).symm
  have bound := (BitVec.extractLsb' 0 2 address).isLt
  have cases : (BitVec.extractLsb' 0 2 address).toNat = 0 ∨
      (BitVec.extractLsb' 0 2 address).toNat = 1 ∨
      (BitVec.extractLsb' 0 2 address).toNat = 2 ∨
      (BitVec.extractLsb' 0 2 address).toNat = 3 := by omega
  rcases cases with h | h | h | h
  · have eq : BitVec.extractLsb' 0 2 address = 0#2 := BitVec.eq_of_toNat_eq h
    rw [eq] at bit0 bit1
    simp [loadData_v732, loadData_v731, loadData_v730, loadData_v729,
      loadData_v728, loadData_v727, loadData_v726, loadData_v725, loadData_v724,
      loadData_v723, loadData_v722, loadData_v721, loadData_v720, loadData_v225,
      loadData_v261, loadData_v2111, loadData_v2110, loadData_v2109, loadData_v2104,
      bit0, bit1, eq]
  · have eq : BitVec.extractLsb' 0 2 address = 1#2 := BitVec.eq_of_toNat_eq h
    rw [eq] at bit0 bit1
    simp [loadData_v732, loadData_v731, loadData_v730, loadData_v729,
      loadData_v728, loadData_v727, loadData_v726, loadData_v725, loadData_v724,
      loadData_v723, loadData_v722, loadData_v721, loadData_v720, loadData_v225,
      loadData_v261, loadData_v2111, loadData_v2110, loadData_v2109, loadData_v2104,
      bit0, bit1, eq]
  · have eq : BitVec.extractLsb' 0 2 address = 2#2 := BitVec.eq_of_toNat_eq h
    rw [eq] at bit0 bit1
    simp [loadData_v732, loadData_v731, loadData_v730, loadData_v729,
      loadData_v728, loadData_v727, loadData_v726, loadData_v725, loadData_v724,
      loadData_v723, loadData_v722, loadData_v721, loadData_v720, loadData_v225,
      loadData_v261, loadData_v2111, loadData_v2110, loadData_v2109, loadData_v2104,
      bit0, bit1, eq]
  · have eq : BitVec.extractLsb' 0 2 address = 3#2 := BitVec.eq_of_toNat_eq h
    rw [eq] at bit0 bit1
    simp [loadData_v732, loadData_v731, loadData_v730, loadData_v729,
      loadData_v728, loadData_v727, loadData_v726, loadData_v725, loadData_v724,
      loadData_v723, loadData_v722, loadData_v721, loadData_v720, loadData_v225,
      loadData_v261, loadData_v2111, loadData_v2110, loadData_v2109, loadData_v2104,
      bit0, bit1, eq]

theorem load_shifted_response (kind : BitVec 3) (address response : BitVec 32) :
    loadData_v733 kind address response = loadData_v2112 0 address response := by
  unfold loadData_v733 loadData_v2112
  rw [load_shift_amount]

#print axioms load_shift_amount
#print axioms load_shifted_response
end RiscvMiniProofs
