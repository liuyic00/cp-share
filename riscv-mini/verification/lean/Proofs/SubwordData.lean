import Proofs.LoadShift
namespace RiscvMiniProofs
set_option linter.unusedSimpArgs false
theorem load_mask_8 (word : BitVec 32) :
    BitVec.extractLsb' 0 8 (((0#32) ++ word) &&& (255#64)) =
      BitVec.extractLsb' 0 8 word := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have mask : (255#64).getLsbD j = true := by
    change ((0#56) ++ BitVec.allOnes 8).getLsbD j = true
    simp only [BitVec.getLsbD_append, hj, ↓reduceIte, BitVec.getLsbD_allOnes, decide_true]
  simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_and,
    BitVec.getLsbD_append (n := 32) (m := 32), hj, show j < 32 by omega, mask]
#print axioms load_mask_8

theorem load_mask_16 (word : BitVec 32) :
    BitVec.extractLsb' 0 16 (((0#32) ++ word) &&& (65535#64)) =
      BitVec.extractLsb' 0 16 word := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have mask : (65535#64).getLsbD j = true := by
    change ((0#48) ++ BitVec.allOnes 16).getLsbD j = true
    simp only [BitVec.getLsbD_append, hj, ↓reduceIte, BitVec.getLsbD_allOnes, decide_true]
  simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_and,
    BitVec.getLsbD_append (n := 32) (m := 32), hj, show j < 32 by omega, mask]
#print axioms load_mask_16

theorem reference_lbu_data (address response : BitVec 32) :
    loadData_v2132 0 address response =
      (0#24) ++ BitVec.extractLsb' 0 8 (loadData_v2112 0 address response) := by
  change (0#24) ++ BitVec.extractLsb' 0 8
    (((0#32) ++ loadData_v2112 0 address response) &&& (255#64)) = _
  rw [load_mask_8]

theorem reference_lhu_data (address response : BitVec 32) :
    loadData_v2117 0 address response =
      (0#16) ++ BitVec.extractLsb' 0 16 (loadData_v2112 0 address response) := by
  exact congrArg (fun x : BitVec 16 => (0#16) ++ x)
    (load_mask_16 (loadData_v2112 0 address response))

theorem dut_lbu_data (address response : BitVec 32) :
    dutLoadData 5 address response =
      (0#24) ++ BitVec.extractLsb' 0 8 (loadData_v2112 0 address response) := by
  simp only [dutLoadData, loadData_v759, loadData_v717, loadData_v716,
    BitVec.reduceEq, ↓reduceIte, loadData_v738, loadData_v737, loadData_v736,
    loadData_v735, loadData_v734, loadData_v4]
  rw [load_shifted_response]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    BitVec.getLsbD_replicate]
  by_cases lo : j < 8
  · simp [lo, show j < 9 by omega, hj]
  · by_cases edge : j < 9
    · have eq : j = 8 := by omega
      simp [eq]
    · simp [lo, edge, hj, Nat.mod_one]

theorem dut_lhu_data (address response : BitVec 32) :
    dutLoadData 4 address response =
      (0#16) ++ BitVec.extractLsb' 0 16 (loadData_v2112 0 address response) := by
  simp only [dutLoadData, loadData_v759, loadData_v717, loadData_v716,
    BitVec.reduceEq, ↓reduceIte, loadData_v758, loadData_v739, loadData_v22,
    loadData_v744, loadData_v743, loadData_v742, loadData_v741, loadData_v740, loadData_v4]
  rw [load_shifted_response]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    BitVec.getLsbD_replicate]
  by_cases lo : j < 16
  · simp [lo, show j < 17 by omega, hj]
  · by_cases edge : j < 17
    · have eq : j = 16 := by omega
      simp [eq]
    · simp [lo, edge, hj, Nat.mod_one]

#print axioms dut_lbu_data
theorem unsigned_byte_data_agrees (address response : BitVec 32) :
    dutLoadData 5 address response = loadData_v2132 0 address response :=
  (dut_lbu_data address response).trans (reference_lbu_data address response).symm

theorem unsigned_half_data_agrees (address response : BitVec 32) :
    dutLoadData 4 address response = loadData_v2117 0 address response :=
  (dut_lhu_data address response).trans (reference_lhu_data address response).symm

#print axioms unsigned_byte_data_agrees
#print axioms unsigned_half_data_agrees
end RiscvMiniProofs
