import Proofs.StoreDataFormat
import Proofs.MemorySizeRun
namespace NutShellProofs
open nNutCore
theorem store_checker_data_size_8 (s : State) (i : Inputs)
    (size : v31337 s i = 8) :
    v31285 s i = (BitVec.extractLsb' 0 8 (v30873 s i)).setWidth 64 := by
  have count : v31264 s i = 1 := by
    have h := congrArg (BitVec.extractLsb' 3 4) size
    change BitVec.extractLsb' 3 4 ((v31264 s i) ++ (0 : BitVec 3)) = BitVec.extractLsb' 3 4 (8 : BitVec 7) at h
    simpa [BitVec.extractLsb'_append_eq_of_le (by decide : 3 ≤ 3), BitVec.extractLsb'_eq_self] using h
  simp [v31285, v31284, v31283, v31282, v31265, v8270, v31281, v11103, v31280, v31267, v31266, v31268, v31279, v9740, v31278, v31270, v31269, v31271, v31277, v12363, v31276, v31273, v31272, v31274, v31275, count, BitVec.setWidth_eq_append]
  simp [HAppend.hAppend, BitVec.instHAppendHAddNat, BitVec.append, BitVec.shiftLeftZeroExtend]
#print axioms store_checker_data_size_8
theorem store_checker_data_size_16 (s : State) (i : Inputs)
    (size : v31337 s i = 16) :
    v31285 s i = (BitVec.extractLsb' 0 16 (v30873 s i)).setWidth 64 := by
  have count : v31264 s i = 2 := by
    have h := congrArg (BitVec.extractLsb' 3 4) size
    change BitVec.extractLsb' 3 4 ((v31264 s i) ++ (0 : BitVec 3)) = BitVec.extractLsb' 3 4 (16 : BitVec 7) at h
    simpa [BitVec.extractLsb'_append_eq_of_le (by decide : 3 ≤ 3), BitVec.extractLsb'_eq_self] using h
  simp [v31285, v31284, v31283, v31282, v31265, v8270, v31281, v11103, v31280, v31267, v31266, v31268, v31279, v9740, v31278, v31270, v31269, v31271, v31277, v12363, v31276, v31273, v31272, v31274, v31275, count, BitVec.setWidth_eq_append]
  simp [HAppend.hAppend, BitVec.instHAppendHAddNat, BitVec.append, BitVec.shiftLeftZeroExtend]
#print axioms store_checker_data_size_16
theorem store_checker_data_size_32 (s : State) (i : Inputs)
    (size : v31337 s i = 32) :
    v31285 s i = (BitVec.extractLsb' 0 32 (v30873 s i)).setWidth 64 := by
  have count : v31264 s i = 4 := by
    have h := congrArg (BitVec.extractLsb' 3 4) size
    change BitVec.extractLsb' 3 4 ((v31264 s i) ++ (0 : BitVec 3)) = BitVec.extractLsb' 3 4 (32 : BitVec 7) at h
    simpa [BitVec.extractLsb'_append_eq_of_le (by decide : 3 ≤ 3), BitVec.extractLsb'_eq_self] using h
  simp [v31285, v31284, v31283, v31282, v31265, v8270, v31281, v11103, v31280, v31267, v31266, v31268, v31279, v9740, v31278, v31270, v31269, v31271, v31277, v12363, v31276, v31273, v31272, v31274, v31275, count, BitVec.setWidth_eq_append]
#print axioms store_checker_data_size_32
theorem store_checker_data_size_64 (s : State) (i : Inputs)
    (size : v31337 s i = 64) :
    v31285 s i = (BitVec.extractLsb' 0 64 (v30873 s i)).setWidth 64 := by
  have count : v31264 s i = 8 := by
    have h := congrArg (BitVec.extractLsb' 3 4) size
    change BitVec.extractLsb' 3 4 ((v31264 s i) ++ (0 : BitVec 3)) = BitVec.extractLsb' 3 4 (64 : BitVec 7) at h
    simpa [BitVec.extractLsb'_append_eq_of_le (by decide : 3 ≤ 3), BitVec.extractLsb'_eq_self] using h
  simp [v31285, v31284, v31283, v31282, v31265, v8270, v31281, v11103, v31280, v31267, v31266, v31268, v31279, v9740, v31278, v31270, v31269, v31271, v31277, v12363, v31276, v31273, v31272, v31274, v31275, count, BitVec.setWidth_eq_append]
#print axioms store_checker_data_size_64
end NutShellProofs
