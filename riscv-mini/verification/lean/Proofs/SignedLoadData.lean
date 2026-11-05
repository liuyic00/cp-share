import Proofs.SubwordData
namespace RiscvMiniProofs
set_option linter.unusedSimpArgs false
theorem lb_sign_replicate (x : BitVec 8) :
    BitVec.extractLsb' 0 32 ((BitVec.replicate 25 (BitVec.extractLsb' 7 1 x)) ++ x) = x.signExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    BitVec.getLsbD_replicate, BitVec.getLsbD_signExtend]
  by_cases lo : j < 8
  · simp [lo, hj]
  · simp [lo, hj, Nat.mod_one, show j-8 < 25 by omega, BitVec.msb_eq_getLsbD_last]

theorem lb_sign_conditional (x : BitVec 8) :
    ((if BitVec.extractLsb' 7 1 x = 1 then (16777215#24) else (0#24)) ++ x) =
      x.signExtend 32 := by
  have bit : BitVec.extractLsb' 7 1 x = BitVec.ofBool x.msb := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have eq : j = 0 := by omega
    subst j
    simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofBool, BitVec.msb_eq_getLsbD_last]
  rw [bit, BitVec.signExtend_eq_append_of_le (by decide)]
  cases h : x.msb <;> simp [h] <;> rfl

theorem dut_lb_data (address response : BitVec 32) :
    dutLoadData 3 address response =
      (BitVec.extractLsb' 0 8 (loadData_v2112 0 address response)).signExtend 32 := by
  simp only [dutLoadData, loadData_v759, loadData_v717, loadData_v716, loadData_v758, loadData_v739, loadData_v22, loadData_v757, loadData_v745, loadData_v200, loadData_v749, loadData_v748, loadData_v747, loadData_v746, BitVec.reduceEq, ↓reduceIte]
  rw [load_shifted_response]
  exact lb_sign_replicate _

theorem reference_lb_data (address response : BitVec 32) :
    loadData_v2193 0 address response =
      (BitVec.extractLsb' 0 8 (loadData_v2112 0 address response)).signExtend 32 := by
  change ((if BitVec.extractLsb' 7 1 (BitVec.extractLsb' 0 8
    ((0#32 ++ loadData_v2112 0 address response) &&& 255#64)) = 1
    then 16777215#24 else 0#24) ++ BitVec.extractLsb' 0 8
    ((0#32 ++ loadData_v2112 0 address response) &&& 255#64)) = (BitVec.extractLsb' 0 8 (loadData_v2112 0 address response)).signExtend 32
  rw [load_mask_8]
  exact lb_sign_conditional _

theorem lb_data_agrees (address response : BitVec 32) :
    dutLoadData 3 address response = loadData_v2193 0 address response :=
  (dut_lb_data address response).trans (reference_lb_data address response).symm
#print axioms lb_data_agrees

theorem lh_sign_replicate (x : BitVec 16) :
    BitVec.extractLsb' 0 32 ((BitVec.replicate 17 (BitVec.extractLsb' 15 1 x)) ++ x) = x.signExtend 32 := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append,
    BitVec.getLsbD_replicate, BitVec.getLsbD_signExtend]
  by_cases lo : j < 16
  · simp [lo, hj]
  · simp [lo, hj, Nat.mod_one, show j-16 < 17 by omega, BitVec.msb_eq_getLsbD_last]

theorem lh_sign_conditional (x : BitVec 16) :
    ((if BitVec.extractLsb' 15 1 x = 1 then (65535#16) else (0#16)) ++ x) =
      x.signExtend 32 := by
  have bit : BitVec.extractLsb' 15 1 x = BitVec.ofBool x.msb := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    have eq : j = 0 := by omega
    subst j
    simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_ofBool, BitVec.msb_eq_getLsbD_last]
  rw [bit, BitVec.signExtend_eq_append_of_le (by decide)]
  cases h : x.msb <;> simp [h] <;> rfl

theorem dut_lh_data (address response : BitVec 32) :
    dutLoadData 2 address response =
      (BitVec.extractLsb' 0 16 (loadData_v2112 0 address response)).signExtend 32 := by
  simp only [dutLoadData, loadData_v759, loadData_v717, loadData_v716, loadData_v758, loadData_v739, loadData_v22, loadData_v757, loadData_v745, loadData_v200, loadData_v756, loadData_v750, loadData_v26, loadData_v754, loadData_v753, loadData_v752, loadData_v751, BitVec.reduceEq, ↓reduceIte]
  rw [load_shifted_response]
  exact lh_sign_replicate _

theorem reference_lh_data (address response : BitVec 32) :
    loadData_v2176 0 address response =
      (BitVec.extractLsb' 0 16 (loadData_v2112 0 address response)).signExtend 32 := by
  change ((if BitVec.extractLsb' 15 1 (BitVec.extractLsb' 0 16
    ((0#32 ++ loadData_v2112 0 address response) &&& 65535#64)) = 1
    then 65535#16 else 0#16) ++ BitVec.extractLsb' 0 16
    ((0#32 ++ loadData_v2112 0 address response) &&& 65535#64)) = (BitVec.extractLsb' 0 16 (loadData_v2112 0 address response)).signExtend 32
  rw [load_mask_16]
  exact lh_sign_conditional _

theorem lh_data_agrees (address response : BitVec 32) :
    dutLoadData 2 address response = loadData_v2176 0 address response :=
  (dut_lh_data address response).trans (reference_lh_data address response).symm
#print axioms lh_data_agrees

end RiscvMiniProofs
