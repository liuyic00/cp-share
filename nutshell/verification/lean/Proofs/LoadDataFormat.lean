import Proofs.MemoryPipeline
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
theorem load_lb_formatted_result (s : State) (i : Inputs)
    (op : v28 s i = MemoryOp.control .lb)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0) :
    v12460 s i = ((if BitVec.extractLsb' 7 1 (BitVec.extractLsb' 0 8 (v12412 s i)) = 1 then (72057594037927935 : BitVec 56) else 0) ++ (BitVec.extractLsb' 0 8 (v12412 s i))) := by
  simp [v12460, v11644, v11641, v11571, v11570, v24, v11643, v11642, v12459, v12452, v12445, v12438, v12429, v12419, v12357, v12356, v12417, v12416, v12414, v12413, v12415, v12406, v12418, v12428, v12421, v12420, v12426, v12425, v12423, v12422, v12424, v12399, v12427, v12437, v12431, v12430, v12435, v12434, v12433, v12432, v11488, v11103, v12436, v12444, v12440, v12439, v12442, v12441, v12443, v12451, v12447, v12446, v12449, v12448, v12450, v12458, v12454, v12453, v12456, v12455, v12457, v11569, v11568, v11519, v2687, outer, v11526, op, MemoryOp.control]
#print axioms load_lb_formatted_result
theorem load_lh_formatted_result (s : State) (i : Inputs)
    (op : v28 s i = MemoryOp.control .lh)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0) :
    v12460 s i = ((if BitVec.extractLsb' 15 1 (BitVec.extractLsb' 0 16 (v12412 s i)) = 1 then (281474976710655 : BitVec 48) else 0) ++ (BitVec.extractLsb' 0 16 (v12412 s i))) := by
  simp [v12460, v11644, v11641, v11571, v11570, v24, v11643, v11642, v12459, v12452, v12445, v12438, v12429, v12419, v12357, v12356, v12417, v12416, v12414, v12413, v12415, v12406, v12418, v12428, v12421, v12420, v12426, v12425, v12423, v12422, v12424, v12399, v12427, v12437, v12431, v12430, v12435, v12434, v12433, v12432, v11488, v11103, v12436, v12444, v12440, v12439, v12442, v12441, v12443, v12451, v12447, v12446, v12449, v12448, v12450, v12458, v12454, v12453, v12456, v12455, v12457, v11569, v11568, v11519, v2687, outer, v11526, op, MemoryOp.control]
#print axioms load_lh_formatted_result
theorem load_lw_formatted_result (s : State) (i : Inputs)
    (op : v28 s i = MemoryOp.control .lw)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0) :
    v12460 s i = ((if BitVec.extractLsb' 31 1 (BitVec.extractLsb' 0 32 (v12412 s i)) = 1 then (4294967295 : BitVec 32) else 0) ++ (BitVec.extractLsb' 0 32 (v12412 s i))) := by
  simp [v12460, v11644, v11641, v11571, v11570, v24, v11643, v11642, v12459, v12452, v12445, v12438, v12429, v12419, v12357, v12356, v12417, v12416, v12414, v12413, v12415, v12406, v12418, v12428, v12421, v12420, v12426, v12425, v12423, v12422, v12424, v12399, v12427, v12437, v12431, v12430, v12435, v12434, v12433, v12432, v11488, v11103, v12436, v12444, v12440, v12439, v12442, v12441, v12443, v12451, v12447, v12446, v12449, v12448, v12450, v12458, v12454, v12453, v12456, v12455, v12457, v11569, v11568, v11519, v2687, outer, v11526, op, MemoryOp.control]
#print axioms load_lw_formatted_result
theorem load_ld_formatted_result (s : State) (i : Inputs)
    (op : v28 s i = MemoryOp.control .ld)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0) :
    v12460 s i = v12306 s i := by
  simp [v12460, v11644, v11641, v11571, v11570, v24, v11643, v11642, v12459, v12452, v12445, v12438, v12429, v12419, v12357, v12356, v12417, v12416, v12414, v12413, v12415, v12406, v12418, v12428, v12421, v12420, v12426, v12425, v12423, v12422, v12424, v12399, v12427, v12437, v12431, v12430, v12435, v12434, v12433, v12432, v11488, v11103, v12436, v12444, v12440, v12439, v12442, v12441, v12443, v12451, v12447, v12446, v12449, v12448, v12450, v12458, v12454, v12453, v12456, v12455, v12457, v11569, v11568, v11519, v2687, outer, v11526, op, MemoryOp.control]
#print axioms load_ld_formatted_result
theorem load_lbu_formatted_result (s : State) (i : Inputs)
    (op : v28 s i = MemoryOp.control .lbu)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0) :
    v12460 s i = ((0 : BitVec 56) ++ (BitVec.extractLsb' 0 8 (v12412 s i))) := by
  simp [v12460, v11644, v11641, v11571, v11570, v24, v11643, v11642, v12459, v12452, v12445, v12438, v12429, v12419, v12357, v12356, v12417, v12416, v12414, v12413, v12415, v12406, v12418, v12428, v12421, v12420, v12426, v12425, v12423, v12422, v12424, v12399, v12427, v12437, v12431, v12430, v12435, v12434, v12433, v12432, v11488, v11103, v12436, v12444, v12440, v12439, v12442, v12441, v12443, v12451, v12447, v12446, v12449, v12448, v12450, v12458, v12454, v12453, v12456, v12455, v12457, v11569, v11568, v11519, v2687, outer, v11526, op, MemoryOp.control]
#print axioms load_lbu_formatted_result
theorem load_lhu_formatted_result (s : State) (i : Inputs)
    (op : v28 s i = MemoryOp.control .lhu)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0) :
    v12460 s i = ((0 : BitVec 48) ++ (BitVec.extractLsb' 0 16 (v12412 s i))) := by
  simp [v12460, v11644, v11641, v11571, v11570, v24, v11643, v11642, v12459, v12452, v12445, v12438, v12429, v12419, v12357, v12356, v12417, v12416, v12414, v12413, v12415, v12406, v12418, v12428, v12421, v12420, v12426, v12425, v12423, v12422, v12424, v12399, v12427, v12437, v12431, v12430, v12435, v12434, v12433, v12432, v11488, v11103, v12436, v12444, v12440, v12439, v12442, v12441, v12443, v12451, v12447, v12446, v12449, v12448, v12450, v12458, v12454, v12453, v12456, v12455, v12457, v11569, v11568, v11519, v2687, outer, v11526, op, MemoryOp.control]
#print axioms load_lhu_formatted_result
theorem load_lwu_formatted_result (s : State) (i : Inputs)
    (op : v28 s i = MemoryOp.control .lwu)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0) :
    v12460 s i = ((0 : BitVec 32) ++ (BitVec.extractLsb' 0 32 (v12412 s i))) := by
  simp [v12460, v11644, v11641, v11571, v11570, v24, v11643, v11642, v12459, v12452, v12445, v12438, v12429, v12419, v12357, v12356, v12417, v12416, v12414, v12413, v12415, v12406, v12418, v12428, v12421, v12420, v12426, v12425, v12423, v12422, v12424, v12399, v12427, v12437, v12431, v12430, v12435, v12434, v12433, v12432, v11488, v11103, v12436, v12444, v12440, v12439, v12442, v12441, v12443, v12451, v12447, v12446, v12449, v12448, v12450, v12458, v12454, v12453, v12456, v12455, v12457, v11569, v11568, v11519, v2687, outer, v11526, op, MemoryOp.control]
#print axioms load_lwu_formatted_result
end NutShellProofs
