import Proofs.Assembly
namespace NutShellProofs
open nNutCore

/-- A four-byte-aligned buffer offset cannot enter the forbidden cross-boundary
case checked by original assertion zero. Alignment is a remaining obligation. -/
theorem frontend_task0_of_offset_aligned (s : State) (i : Inputs)
    (aligned : BitVec.extractLsb' 0 2 (v9735 s i) = 0) : TaskHolds 0 s i := by
  have notSix : v9735 s i ≠ (BitVec.ofNat 3 6) := by
    intro six
    rw [six] at aligned
    contradiction
  change decide (v30882 s i ≠ 1 ∨ v30881 s i = 1) = true
  simp [v30881, v30880, v30878, v30877, v9809, v9806, v9804, v97, notSix, v24]

/-- A marked crossing also satisfies the original assertion independently of
buffer offset. This preserves the original allowed crossing behavior. -/
theorem frontend_task0_of_crossing_marked (s : State) (i : Inputs)
    (marked : BitVec.extractLsb' 3 1 (v9795 s i) = 1) : TaskHolds 0 s i := by
  change decide (v30882 s i ≠ 1 ∨ v30881 s i = 1) = true
  simp [v30881, v30880, v30879, v11078, marked, v24]

/-- Empty input buffers cannot trigger the original frontend assertion. -/
theorem frontend_task0_of_empty (s : State) (i : Inputs)
    (empty : v9802 s i = 0) : TaskHolds 0 s i := by
  change decide (v30882 s i ≠ 1 ∨ v30881 s i = 1) = true
  simp [v30881, v30880, v30878, empty, v24]
#print axioms frontend_task0_of_offset_aligned
#print axioms frontend_task0_of_crossing_marked
#print axioms frontend_task0_of_empty
end NutShellProofs
