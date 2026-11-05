import Proofs.MemoryRequestHold
namespace NutShellProofs
open nNutCore

theorem memory_raw_alignment_excludes_fault (s : State) (i : Inputs)
    (aligned : v11628 s i = 1) : v11639 s i = 0 ∧ v11640 s i = 0 := by
  simp [v11639, v11640, v11632, v11638, v11631, v11637,
    v11630, v11636, v11629, v11635, aligned, v24]

theorem memory_request_raw_alignment (s : State) (i : Inputs)
    (request : v12570 s i = 1) : v11628 s i = 1 := by
  have enabled : v11546 s i = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v11546 s i) with zero | one
    · simp [v12570, v12569, v12263, v12262, v12260, v12258, zero] at request
    · exact one
  have faults := (memory_request_has_no_alignment_fault s i request).1
  rcases BitVec.eq_zero_or_eq_one (v11628 s i) with zero | one
  · rcases BitVec.eq_zero_or_eq_one (v11570 s i) with a | a <;>
      rcases BitVec.eq_zero_or_eq_one (v11584 s i) with b | b <;>
      simp [v11639, v11632, v11638, v11631, v11637, v11630, v11636,
        v11629, v11635, v11634, v11633, v11586, v11585, v11573,
        v11572, v11571, enabled, zero, a, b, v24] at faults
  · exact one

theorem memory_raw_alignment_hold (s : State) (i next : Inputs)
    (idle : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (nextIdle : (step s i).g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (hold : v24283 s i ≠ 1) : v11628 (step s i) next = v11628 s i := by
  have address := lsu_address_hold_without_capture s i next idle nextIdle hold
  have op : v11569 (step s i) next = v11569 s i := by
    simp only [v11569, v11568, v11519, v2687, idle, nextIdle, ↓reduceIte, v11526]
    change v24928 s i = v28 s i
    simp only [v24928, hold, ↓reduceIte, v28]
  simp only [v11628, v11622, v11627, v11616, v11621, v11623, v11626,
    v11624, v11625, v11589, v11615, v11591, v11614, v11613,
    v11617, v11620, v11618, v11619, v11587, v11588, v11590,
    address, op, v24, v9721, v2750]

#print axioms memory_raw_alignment_excludes_fault
#print axioms memory_request_raw_alignment
#print axioms memory_raw_alignment_hold
theorem memory_request_next_alignment (s : State) (i next : Inputs)
    (operation : MemoryOp) (op : v28 s i = operation.control)
    (idle : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (nextIdle : (step s i).g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (unit : v3 s i = 1) (valid : v6 s i = 1)
    (request : v12570 s i = 1) :
    v11628 (step s i) next = 1 ∧
      v11639 (step s i) next = 0 ∧ v11640 (step s i) next = 0 := by
  have hold := memory_request_prevents_execute_capture s i operation op idle unit valid request
  have aligned : v11628 (step s i) next = 1 :=
    (memory_raw_alignment_hold s i next idle nextIdle hold).trans
      (memory_request_raw_alignment s i request)
  exact ⟨aligned, memory_raw_alignment_excludes_fault _ _ aligned⟩

#print axioms memory_request_next_alignment
end NutShellProofs
