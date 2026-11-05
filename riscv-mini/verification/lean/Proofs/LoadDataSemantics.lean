import Proofs.LoadDataCone
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedSimpArgs false

theorem dut_load_word (address response : BitVec 32) :
    dutLoadData 1 address response = response := by
  simp [dutLoadData, loadData_v759, loadData_v717, loadData_v716, loadData_v758, loadData_v739, loadData_v22, loadData_v757, loadData_v745, loadData_v200, loadData_v756, loadData_v750, loadData_v26, loadData_v755, loadData_v4]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [BitVec.getLsbD_append (n := 1) (m := 32), hj]

theorem reference_load_word (address response : BitVec 32)
    (aligned : BitVec.extractLsb' 0 2 address = 0) :
    loadData_v2153 0 address response = response := by
  have eq : BitVec.extractLsb' 0 2 address = 0#2 := aligned
  simp [loadData_v2153, loadData_v2152, loadData_v2151, loadData_v2150, loadData_v2149, loadData_v2148, loadData_v2147, loadData_v2146, loadData_v2104, loadData_v261, loadData_v3, eq]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have mask : (4294967295#64).getLsbD j = true := by
    change ((0#32) ++ BitVec.allOnes 32).getLsbD j = true
    simp only [BitVec.getLsbD_append, hj, ↓reduceIte, BitVec.getLsbD_allOnes, decide_true]
  simp [BitVec.getLsbD_and, BitVec.getLsbD_append (n := 32) (m := 32), hj, mask]

#print axioms dut_load_word
#print axioms reference_load_word
end RiscvMiniProofs
