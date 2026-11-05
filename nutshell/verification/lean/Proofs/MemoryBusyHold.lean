import Proofs.MemoryAddressInterval
namespace NutShellProofs
open nNutCore

theorem memory_next_busy_prevents_capture (s : State) (i : Inputs)
    (operation : MemoryOp) (op : v28 s i = operation.control)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (reachable : LSUInnerReachable s)
    (unit : v3 s i = 1) (valid : v6 s i = 1)
    (noFault : v11639 s i = 0) (aligned : v11640 s i = 0)
    (nextBusy : (step s i).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate ≠ 0) :
    v24283 s i ≠ 1 := by
  have incomplete : v11698 s i = 0 := by
    rcases BitVec.eq_zero_or_eq_one (v11698 s i) with zero | one
    · exact zero
    · exact False.elim (nextBusy (normal_memory_completion_returns_inner_idle s i
        operation op outer reachable noFault aligned one))
  intro capture
  have complete := execute_capture_replaces_only_completed s i valid capture
  simp [v11702, v11701, v11700, v11495, v11494, unit, v11699,
    v11518, v11517, incomplete] at complete

theorem memory_busy_address_latched_step (s : State) (i next : Inputs)
    (operation : MemoryOp) (op : v28 s i = operation.control)
    (reset : i.g0.nreset = 0)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (nextOuter : (step s i).g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (reachable : LSUInnerReachable s)
    (unit : v3 s i = 1) (valid : v6 s i = 1)
    (noFault : v11639 s i = 0) (aligned : v11640 s i = 0)
    (nextBusy : (step s i).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate ≠ 0)
    (old : s.g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate ≠ 0 → MemoryAddressLatched s i) :
    MemoryAddressLatched (step s i) next := by
  have hold := memory_next_busy_prevents_capture s i operation op outer reachable unit valid noFault aligned nextBusy
  rcases lsu_inner_busy_predecessor s i nextBusy with prior | request
  · exact memory_address_latched_hold s i next reset unit outer nextOuter hold (old prior)
  · exact memory_address_latched_after_request s i next reset unit request outer nextOuter hold
#print axioms memory_next_busy_prevents_capture
#print axioms memory_busy_address_latched_step
end NutShellProofs
