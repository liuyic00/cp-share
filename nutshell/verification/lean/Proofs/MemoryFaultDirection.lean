import Proofs.MemoryMisalignment
namespace NutShellProofs
open nNutCore

/-- Ordinary decoded operations select precisely their own alignment fault. -/
theorem normal_memory_fault_direction (s : State) (i : Inputs)
    (operation : MemoryOp) (op : v28 s i = operation.control)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (enabled : v11546 s i = 1) :
    v11632 s i = (if operation.isLoad && (v11628 s i == 0) then 1 else 0) ∧
    v11638 s i = (if !operation.isLoad && (v11628 s i == 0) then 1 else 0) := by
  have effective : v11569 s i = operation.control := by
    simp [v11569, v11568, v11519, v2687, outer, v11526, op]
  have atomic : v11584 s i = 0 := by
    cases operation <;>
      simp [v11584, v11583, v11582, v11578, v11574, v11526, op, MemoryOp.control]
  cases operation <;>
    rcases BitVec.eq_zero_or_eq_one (v11628 s i) with aligned | aligned <;>
    simp [v11632, v11631, v11630, v11629, v11638, v11637, v11636,
      v11635, v11634, v11633, v11586, v11585, v11573, v11572, v11571,
      v11570, effective, atomic, enabled, aligned, MemoryOp.control, MemoryOp.isLoad, v24]
#print axioms normal_memory_fault_direction
end NutShellProofs
