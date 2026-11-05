import Proofs.StoreCompletedData
namespace NutShellProofs
open nNutCore
theorem store_sb_formatted_low (s : State) (i : Inputs)
    (op : v28 s i = MemoryOp.control .sb)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0) :
    BitVec.extractLsb' 0 8 (v14539 s i) = BitVec.extractLsb' 0 8 (v12150 s i) := by
  simp [v14539, v14538, v14537, v14536, v14532, v14526, v14518, v14497, v14496, v14454, v14516, v14515, v14514, v14513, v14517, v14525, v14520, v14519, v14523, v14522, v14521, v14524, v14531, v14527, v9721, v14529, v14528, v14530, v14535, v14533, v2750, v14534, v11569, v11568, v11519, v2687, outer, v11526, op, MemoryOp.control,
    v14512, v14511, v12471, v12150]
  simp only [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 8 ≤ 32), BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 8 ≤ 16), BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 8 ≤ 8), BitVec.extractLsb'_eq_self]
#print axioms store_sb_formatted_low
theorem store_sh_formatted_low (s : State) (i : Inputs)
    (op : v28 s i = MemoryOp.control .sh)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0) :
    BitVec.extractLsb' 0 16 (v14539 s i) = BitVec.extractLsb' 0 16 (v12150 s i) := by
  simp [v14539, v14538, v14537, v14536, v14532, v14526, v14518, v14497, v14496, v14454, v14516, v14515, v14514, v14513, v14517, v14525, v14520, v14519, v14523, v14522, v14521, v14524, v14531, v14527, v9721, v14529, v14528, v14530, v14535, v14533, v2750, v14534, v11569, v11568, v11519, v2687, outer, v11526, op, MemoryOp.control,
    v14512, v14511, v12471, v12150]
  simp only [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 16 ≤ 32), BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 16 ≤ 16), BitVec.extractLsb'_eq_self]
#print axioms store_sh_formatted_low
theorem store_sw_formatted_low (s : State) (i : Inputs)
    (op : v28 s i = MemoryOp.control .sw)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0) :
    BitVec.extractLsb' 0 32 (v14539 s i) = BitVec.extractLsb' 0 32 (v12150 s i) := by
  simp [v14539, v14538, v14537, v14536, v14532, v14526, v14518, v14497, v14496, v14454, v14516, v14515, v14514, v14513, v14517, v14525, v14520, v14519, v14523, v14522, v14521, v14524, v14531, v14527, v9721, v14529, v14528, v14530, v14535, v14533, v2750, v14534, v11569, v11568, v11519, v2687, outer, v11526, op, MemoryOp.control,
    v14512, v14511, v12471, v12150]
  simp only [BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 32 ≤ 32), BitVec.extractLsb'_eq_self]
#print axioms store_sw_formatted_low
theorem store_sd_formatted_low (s : State) (i : Inputs)
    (op : v28 s i = MemoryOp.control .sd)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0) :
    BitVec.extractLsb' 0 64 (v14539 s i) = BitVec.extractLsb' 0 64 (v12150 s i) := by
  simp [v14539, v14538, v14537, v14536, v14532, v14526, v14518, v14497, v14496, v14454, v14516, v14515, v14514, v14513, v14517, v14525, v14520, v14519, v14523, v14522, v14521, v14524, v14531, v14527, v9721, v14529, v14528, v14530, v14535, v14533, v2750, v14534, v11569, v11568, v11519, v2687, outer, v11526, op, MemoryOp.control,
    v14512, v14511, v12471, v12150]
#print axioms store_sd_formatted_low
end NutShellProofs
