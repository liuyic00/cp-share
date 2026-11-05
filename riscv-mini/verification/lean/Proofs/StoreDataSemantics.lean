import Proofs.StoreDataCone
import Proofs.JumpImmediate
namespace RiscvMiniProofs
set_option exponentiation.threshold 512
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
theorem store_sb_offset_0 (address source : BitVec 32)
    (offset : BitVec.extractLsb' 0 2 address = 0) :
    checkedStoreData (storeMask 3 address source) address (storeData 3 address source) = (0#24) ++ (BitVec.extractLsb' 0 8 source) := by
  have low : BitVec.extractLsb' 0 1 address = 0 := by
    rw [← extract_prefix address 2 0 1 (by decide), offset]
    rfl
  have high : BitVec.extractLsb' 1 1 address = 0 := by
    rw [← extract_prefix address 2 1 1 (by decide), offset]
    rfl
  simp only [checkedStoreData, storeMask, storeData, storePack_v155, storePack_v8523, storePack_v4, storePack_v8524, storePack_v32, storePack_v8525, storePack_v8526, storePack_v8527, storePack_v8528, storePack_v38, storePack_v8529, storePack_v8530, storePack_v261, storePack_v8531, storePack_v8532, storePack_v8533, storePack_v42, storePack_v8534, storePack_v7794, storePack_v8535, storePack_v8536, storePack_v8537, storePack_v8538, storePack_v8539, storePack_v8540, storePack_v8541, storePack_v8544, storePack_v8545, storePack_v8546, storePack_v720, storePack_v8547, storePack_v8548, storePack_v8549, storePack_v8550, storePack_v725, storePack_v8551, storePack_v8552, storePack_v8553, storePack_v8554, storePack_v8555, storePack_v8556, storePack_v8557, storePack_v8558, storePack_v8559, storePack_v8560, storeUnpack_v9213, storeUnpack_v9214, storeUnpack_v2012, storeUnpack_v9215, storeUnpack_v9216, storeUnpack_v9217, storeUnpack_v9218, storeUnpack_v9219, storeUnpack_v9220, storeUnpack_v9221, storeUnpack_v9222, storeUnpack_v9223, storeUnpack_v9224, storeUnpack_v9225, storeUnpack_v2104, storeUnpack_v155, storeUnpack_v9226, storeUnpack_v9227, storeUnpack_v908, storeUnpack_v38, storeUnpack_v9228, storeUnpack_v860, storeUnpack_v4, storeUnpack_v9229, storeUnpack_v9230, storeUnpack_v7791, storeUnpack_v725, storeUnpack_v9231, storeUnpack_v9232, storeUnpack_v9233, storeUnpack_v9234, storeUnpack_v9235, storeUnpack_v9236, storeUnpack_v9237, offset, low, high]
  simp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 ∨ j = 31 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getElem_append (n := 255) (m := 32), BitVec.getElem_append (n := 24) (m := 8), BitVec.getElem_append (n := 16) (m := 16), BitVec.getElem_extractLsb']
#print axioms store_sb_offset_0
theorem store_sb_offset_1 (address source : BitVec 32)
    (offset : BitVec.extractLsb' 0 2 address = 1) :
    checkedStoreData (storeMask 3 address source) address (storeData 3 address source) = (0#24) ++ (BitVec.extractLsb' 0 8 source) := by
  have low : BitVec.extractLsb' 0 1 address = 1 := by
    rw [← extract_prefix address 2 0 1 (by decide), offset]
    rfl
  have high : BitVec.extractLsb' 1 1 address = 0 := by
    rw [← extract_prefix address 2 1 1 (by decide), offset]
    rfl
  simp only [checkedStoreData, storeMask, storeData, storePack_v155, storePack_v8523, storePack_v4, storePack_v8524, storePack_v32, storePack_v8525, storePack_v8526, storePack_v8527, storePack_v8528, storePack_v38, storePack_v8529, storePack_v8530, storePack_v261, storePack_v8531, storePack_v8532, storePack_v8533, storePack_v42, storePack_v8534, storePack_v7794, storePack_v8535, storePack_v8536, storePack_v8537, storePack_v8538, storePack_v8539, storePack_v8540, storePack_v8541, storePack_v8544, storePack_v8545, storePack_v8546, storePack_v720, storePack_v8547, storePack_v8548, storePack_v8549, storePack_v8550, storePack_v725, storePack_v8551, storePack_v8552, storePack_v8553, storePack_v8554, storePack_v8555, storePack_v8556, storePack_v8557, storePack_v8558, storePack_v8559, storePack_v8560, storeUnpack_v9213, storeUnpack_v9214, storeUnpack_v2012, storeUnpack_v9215, storeUnpack_v9216, storeUnpack_v9217, storeUnpack_v9218, storeUnpack_v9219, storeUnpack_v9220, storeUnpack_v9221, storeUnpack_v9222, storeUnpack_v9223, storeUnpack_v9224, storeUnpack_v9225, storeUnpack_v2104, storeUnpack_v155, storeUnpack_v9226, storeUnpack_v9227, storeUnpack_v908, storeUnpack_v38, storeUnpack_v9228, storeUnpack_v860, storeUnpack_v4, storeUnpack_v9229, storeUnpack_v9230, storeUnpack_v7791, storeUnpack_v725, storeUnpack_v9231, storeUnpack_v9232, storeUnpack_v9233, storeUnpack_v9234, storeUnpack_v9235, storeUnpack_v9236, storeUnpack_v9237, offset, low, high]
  simp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 ∨ j = 31 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getElem_append (n := 255) (m := 32), BitVec.getElem_append (n := 24) (m := 8), BitVec.getElem_append (n := 16) (m := 16), BitVec.getElem_extractLsb']
#print axioms store_sb_offset_1
theorem store_sb_offset_2 (address source : BitVec 32)
    (offset : BitVec.extractLsb' 0 2 address = 2) :
    checkedStoreData (storeMask 3 address source) address (storeData 3 address source) = (0#24) ++ (BitVec.extractLsb' 0 8 source) := by
  have low : BitVec.extractLsb' 0 1 address = 0 := by
    rw [← extract_prefix address 2 0 1 (by decide), offset]
    rfl
  have high : BitVec.extractLsb' 1 1 address = 1 := by
    rw [← extract_prefix address 2 1 1 (by decide), offset]
    rfl
  simp only [checkedStoreData, storeMask, storeData, storePack_v155, storePack_v8523, storePack_v4, storePack_v8524, storePack_v32, storePack_v8525, storePack_v8526, storePack_v8527, storePack_v8528, storePack_v38, storePack_v8529, storePack_v8530, storePack_v261, storePack_v8531, storePack_v8532, storePack_v8533, storePack_v42, storePack_v8534, storePack_v7794, storePack_v8535, storePack_v8536, storePack_v8537, storePack_v8538, storePack_v8539, storePack_v8540, storePack_v8541, storePack_v8544, storePack_v8545, storePack_v8546, storePack_v720, storePack_v8547, storePack_v8548, storePack_v8549, storePack_v8550, storePack_v725, storePack_v8551, storePack_v8552, storePack_v8553, storePack_v8554, storePack_v8555, storePack_v8556, storePack_v8557, storePack_v8558, storePack_v8559, storePack_v8560, storeUnpack_v9213, storeUnpack_v9214, storeUnpack_v2012, storeUnpack_v9215, storeUnpack_v9216, storeUnpack_v9217, storeUnpack_v9218, storeUnpack_v9219, storeUnpack_v9220, storeUnpack_v9221, storeUnpack_v9222, storeUnpack_v9223, storeUnpack_v9224, storeUnpack_v9225, storeUnpack_v2104, storeUnpack_v155, storeUnpack_v9226, storeUnpack_v9227, storeUnpack_v908, storeUnpack_v38, storeUnpack_v9228, storeUnpack_v860, storeUnpack_v4, storeUnpack_v9229, storeUnpack_v9230, storeUnpack_v7791, storeUnpack_v725, storeUnpack_v9231, storeUnpack_v9232, storeUnpack_v9233, storeUnpack_v9234, storeUnpack_v9235, storeUnpack_v9236, storeUnpack_v9237, offset, low, high]
  simp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 ∨ j = 31 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getElem_append (n := 255) (m := 32), BitVec.getElem_append (n := 24) (m := 8), BitVec.getElem_append (n := 16) (m := 16), BitVec.getElem_extractLsb']
#print axioms store_sb_offset_2
theorem store_sb_offset_3 (address source : BitVec 32)
    (offset : BitVec.extractLsb' 0 2 address = 3) :
    checkedStoreData (storeMask 3 address source) address (storeData 3 address source) = (0#24) ++ (BitVec.extractLsb' 0 8 source) := by
  have low : BitVec.extractLsb' 0 1 address = 1 := by
    rw [← extract_prefix address 2 0 1 (by decide), offset]
    rfl
  have high : BitVec.extractLsb' 1 1 address = 1 := by
    rw [← extract_prefix address 2 1 1 (by decide), offset]
    rfl
  simp only [checkedStoreData, storeMask, storeData, storePack_v155, storePack_v8523, storePack_v4, storePack_v8524, storePack_v32, storePack_v8525, storePack_v8526, storePack_v8527, storePack_v8528, storePack_v38, storePack_v8529, storePack_v8530, storePack_v261, storePack_v8531, storePack_v8532, storePack_v8533, storePack_v42, storePack_v8534, storePack_v7794, storePack_v8535, storePack_v8536, storePack_v8537, storePack_v8538, storePack_v8539, storePack_v8540, storePack_v8541, storePack_v8544, storePack_v8545, storePack_v8546, storePack_v720, storePack_v8547, storePack_v8548, storePack_v8549, storePack_v8550, storePack_v725, storePack_v8551, storePack_v8552, storePack_v8553, storePack_v8554, storePack_v8555, storePack_v8556, storePack_v8557, storePack_v8558, storePack_v8559, storePack_v8560, storeUnpack_v9213, storeUnpack_v9214, storeUnpack_v2012, storeUnpack_v9215, storeUnpack_v9216, storeUnpack_v9217, storeUnpack_v9218, storeUnpack_v9219, storeUnpack_v9220, storeUnpack_v9221, storeUnpack_v9222, storeUnpack_v9223, storeUnpack_v9224, storeUnpack_v9225, storeUnpack_v2104, storeUnpack_v155, storeUnpack_v9226, storeUnpack_v9227, storeUnpack_v908, storeUnpack_v38, storeUnpack_v9228, storeUnpack_v860, storeUnpack_v4, storeUnpack_v9229, storeUnpack_v9230, storeUnpack_v7791, storeUnpack_v725, storeUnpack_v9231, storeUnpack_v9232, storeUnpack_v9233, storeUnpack_v9234, storeUnpack_v9235, storeUnpack_v9236, storeUnpack_v9237, offset, low, high]
  simp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 ∨ j = 31 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getElem_append (n := 255) (m := 32), BitVec.getElem_append (n := 24) (m := 8), BitVec.getElem_append (n := 16) (m := 16), BitVec.getElem_extractLsb']
#print axioms store_sb_offset_3
theorem store_sh_offset_0 (address source : BitVec 32)
    (offset : BitVec.extractLsb' 0 2 address = 0) :
    checkedStoreData (storeMask 2 address source) address (storeData 2 address source) = (0#16) ++ (BitVec.extractLsb' 0 16 source) := by
  have low : BitVec.extractLsb' 0 1 address = 0 := by
    rw [← extract_prefix address 2 0 1 (by decide), offset]
    rfl
  have high : BitVec.extractLsb' 1 1 address = 0 := by
    rw [← extract_prefix address 2 1 1 (by decide), offset]
    rfl
  simp only [checkedStoreData, storeMask, storeData, storePack_v155, storePack_v8523, storePack_v4, storePack_v8524, storePack_v32, storePack_v8525, storePack_v8526, storePack_v8527, storePack_v8528, storePack_v38, storePack_v8529, storePack_v8530, storePack_v261, storePack_v8531, storePack_v8532, storePack_v8533, storePack_v42, storePack_v8534, storePack_v7794, storePack_v8535, storePack_v8536, storePack_v8537, storePack_v8538, storePack_v8539, storePack_v8540, storePack_v8541, storePack_v8544, storePack_v8545, storePack_v8546, storePack_v720, storePack_v8547, storePack_v8548, storePack_v8549, storePack_v8550, storePack_v725, storePack_v8551, storePack_v8552, storePack_v8553, storePack_v8554, storePack_v8555, storePack_v8556, storePack_v8557, storePack_v8558, storePack_v8559, storePack_v8560, storeUnpack_v9213, storeUnpack_v9214, storeUnpack_v2012, storeUnpack_v9215, storeUnpack_v9216, storeUnpack_v9217, storeUnpack_v9218, storeUnpack_v9219, storeUnpack_v9220, storeUnpack_v9221, storeUnpack_v9222, storeUnpack_v9223, storeUnpack_v9224, storeUnpack_v9225, storeUnpack_v2104, storeUnpack_v155, storeUnpack_v9226, storeUnpack_v9227, storeUnpack_v908, storeUnpack_v38, storeUnpack_v9228, storeUnpack_v860, storeUnpack_v4, storeUnpack_v9229, storeUnpack_v9230, storeUnpack_v7791, storeUnpack_v725, storeUnpack_v9231, storeUnpack_v9232, storeUnpack_v9233, storeUnpack_v9234, storeUnpack_v9235, storeUnpack_v9236, storeUnpack_v9237, offset, low, high]
  simp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 ∨ j = 31 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getElem_append (n := 255) (m := 32), BitVec.getElem_append (n := 24) (m := 8), BitVec.getElem_append (n := 16) (m := 16), BitVec.getElem_extractLsb']
#print axioms store_sh_offset_0
theorem store_sh_offset_2 (address source : BitVec 32)
    (offset : BitVec.extractLsb' 0 2 address = 2) :
    checkedStoreData (storeMask 2 address source) address (storeData 2 address source) = (0#16) ++ (BitVec.extractLsb' 0 16 source) := by
  have low : BitVec.extractLsb' 0 1 address = 0 := by
    rw [← extract_prefix address 2 0 1 (by decide), offset]
    rfl
  have high : BitVec.extractLsb' 1 1 address = 1 := by
    rw [← extract_prefix address 2 1 1 (by decide), offset]
    rfl
  simp only [checkedStoreData, storeMask, storeData, storePack_v155, storePack_v8523, storePack_v4, storePack_v8524, storePack_v32, storePack_v8525, storePack_v8526, storePack_v8527, storePack_v8528, storePack_v38, storePack_v8529, storePack_v8530, storePack_v261, storePack_v8531, storePack_v8532, storePack_v8533, storePack_v42, storePack_v8534, storePack_v7794, storePack_v8535, storePack_v8536, storePack_v8537, storePack_v8538, storePack_v8539, storePack_v8540, storePack_v8541, storePack_v8544, storePack_v8545, storePack_v8546, storePack_v720, storePack_v8547, storePack_v8548, storePack_v8549, storePack_v8550, storePack_v725, storePack_v8551, storePack_v8552, storePack_v8553, storePack_v8554, storePack_v8555, storePack_v8556, storePack_v8557, storePack_v8558, storePack_v8559, storePack_v8560, storeUnpack_v9213, storeUnpack_v9214, storeUnpack_v2012, storeUnpack_v9215, storeUnpack_v9216, storeUnpack_v9217, storeUnpack_v9218, storeUnpack_v9219, storeUnpack_v9220, storeUnpack_v9221, storeUnpack_v9222, storeUnpack_v9223, storeUnpack_v9224, storeUnpack_v9225, storeUnpack_v2104, storeUnpack_v155, storeUnpack_v9226, storeUnpack_v9227, storeUnpack_v908, storeUnpack_v38, storeUnpack_v9228, storeUnpack_v860, storeUnpack_v4, storeUnpack_v9229, storeUnpack_v9230, storeUnpack_v7791, storeUnpack_v725, storeUnpack_v9231, storeUnpack_v9232, storeUnpack_v9233, storeUnpack_v9234, storeUnpack_v9235, storeUnpack_v9236, storeUnpack_v9237, offset, low, high]
  simp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 ∨ j = 31 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getElem_append (n := 255) (m := 32), BitVec.getElem_append (n := 24) (m := 8), BitVec.getElem_append (n := 16) (m := 16), BitVec.getElem_extractLsb']
#print axioms store_sh_offset_2
theorem store_sw_offset_0 (address source : BitVec 32)
    (offset : BitVec.extractLsb' 0 2 address = 0) :
    checkedStoreData (storeMask 1 address source) address (storeData 1 address source) = source := by
  have low : BitVec.extractLsb' 0 1 address = 0 := by
    rw [← extract_prefix address 2 0 1 (by decide), offset]
    rfl
  have high : BitVec.extractLsb' 1 1 address = 0 := by
    rw [← extract_prefix address 2 1 1 (by decide), offset]
    rfl
  simp only [checkedStoreData, storeMask, storeData, storePack_v155, storePack_v8523, storePack_v4, storePack_v8524, storePack_v32, storePack_v8525, storePack_v8526, storePack_v8527, storePack_v8528, storePack_v38, storePack_v8529, storePack_v8530, storePack_v261, storePack_v8531, storePack_v8532, storePack_v8533, storePack_v42, storePack_v8534, storePack_v7794, storePack_v8535, storePack_v8536, storePack_v8537, storePack_v8538, storePack_v8539, storePack_v8540, storePack_v8541, storePack_v8544, storePack_v8545, storePack_v8546, storePack_v720, storePack_v8547, storePack_v8548, storePack_v8549, storePack_v8550, storePack_v725, storePack_v8551, storePack_v8552, storePack_v8553, storePack_v8554, storePack_v8555, storePack_v8556, storePack_v8557, storePack_v8558, storePack_v8559, storePack_v8560, storeUnpack_v9213, storeUnpack_v9214, storeUnpack_v2012, storeUnpack_v9215, storeUnpack_v9216, storeUnpack_v9217, storeUnpack_v9218, storeUnpack_v9219, storeUnpack_v9220, storeUnpack_v9221, storeUnpack_v9222, storeUnpack_v9223, storeUnpack_v9224, storeUnpack_v9225, storeUnpack_v2104, storeUnpack_v155, storeUnpack_v9226, storeUnpack_v9227, storeUnpack_v908, storeUnpack_v38, storeUnpack_v9228, storeUnpack_v860, storeUnpack_v4, storeUnpack_v9229, storeUnpack_v9230, storeUnpack_v7791, storeUnpack_v725, storeUnpack_v9231, storeUnpack_v9232, storeUnpack_v9233, storeUnpack_v9234, storeUnpack_v9235, storeUnpack_v9236, storeUnpack_v9237, offset, low, high]
  simp
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 ∨ j = 31 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_and, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_shiftLeft, BitVec.getLsbD_append, BitVec.getElem_append (n := 255) (m := 32), BitVec.getElem_append (n := 24) (m := 8), BitVec.getElem_append (n := 16) (m := 16), BitVec.getElem_extractLsb']
#print axioms store_sw_offset_0
end RiscvMiniProofs
