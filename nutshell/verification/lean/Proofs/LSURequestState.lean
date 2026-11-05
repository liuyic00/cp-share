import Proofs.MemoryAddressHold
namespace NutShellProofs
open nNutCore

theorem lsu_inner_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    (step s i).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 0 := by
  change v12276 s i = 0
  simp [v12276, v12235, v12234, v12103, v11455, reset, v4079]

theorem lsu_inner_idle_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0)
    (idle : s.g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 0) :
    (step s i).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate =
      if v12256 s i &&& v12570 s i = 1 then 2 else 0 := by
  change v12276 s i = _
  simp [v12276, v12235, v12234, v12103, v11455, reset, v12275,
    v12236, v4079, idle, v12265, v12264, v12570, v12569, v12263, v9721]

theorem lsu_inner_wait_entry_requires_request (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0)
    (idle : s.g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 0)
    (waiting : (step s i).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 2) :
    v12570 s i = 1 := by
  rw [lsu_inner_idle_step s i reset idle] at waiting
  rcases BitVec.eq_zero_or_eq_one (v12570 s i) with zero | one
  · simp [zero] at waiting
  · exact one

theorem lsu_wait_entry_latches_address (s : State) (i next : Inputs)
    (reset : i.g0.nreset = 0) (unit : v3 s i = 1)
    (idle : s.g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 0)
    (waiting : (step s i).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 2)
    (outerIdle : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (nextOuterIdle : (step s i).g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (hold : v24283 s i ≠ 1) : MemoryAddressLatched (step s i) next := by
  exact memory_address_latched_after_request s i next reset unit
    (lsu_inner_wait_entry_requires_request s i reset idle waiting) outerIdle nextOuterIdle hold
#print axioms lsu_inner_reset
#print axioms lsu_inner_idle_step
#print axioms lsu_inner_wait_entry_requires_request
#print axioms lsu_wait_entry_latches_address
end NutShellProofs
