import Proofs.MemoryAddressCapture
import Proofs.ExecuteHandshake
namespace NutShellProofs
open nNutCore

theorem lsu_address_hold_without_capture (s : State) (i next : Inputs)
    (idle : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (nextIdle : (step s i).g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (hold : v24283 s i ≠ 1) :
    v11612 (step s i) next = v11612 s i := by
  rw [lsu_address_sum _ _ nextIdle, lsu_address_sum _ _ idle]
  change v25206 s i + v25327 s i = _
  simp only [v25206, v25327, hold, ↓reduceIte]
  rfl

def MemoryAddressLatched (s : State) (i : Inputs) : Prop :=
  s.g44.r1432_nbackend_5Fexu_5Fmem_5Frvfi_5Freg_5Faddr_5Freal =
    ((0 : BitVec 25) ++ BitVec.extractLsb' 0 39 (v11612 s i))

theorem memory_address_latched_after_request (s : State) (i next : Inputs)
    (reset : i.g0.nreset = 0) (unit : v3 s i = 1)
    (request : v12570 s i = 1)
    (idle : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (nextIdle : (step s i).g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (hold : v24283 s i ≠ 1) : MemoryAddressLatched (step s i) next := by
  unfold MemoryAddressLatched
  rw [memory_address_latch_step s i reset unit, if_pos request,
    lsu_address_hold_without_capture s i next idle nextIdle hold]

theorem memory_address_latched_hold (s : State) (i next : Inputs)
    (reset : i.g0.nreset = 0) (unit : v3 s i = 1)
    (idle : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (nextIdle : (step s i).g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (hold : v24283 s i ≠ 1) (old : MemoryAddressLatched s i) :
    MemoryAddressLatched (step s i) next := by
  unfold MemoryAddressLatched at old ⊢
  rw [memory_address_latch_step s i reset unit,
    lsu_address_hold_without_capture s i next idle nextIdle hold]
  split
  · rfl
  · exact old
#print axioms lsu_address_hold_without_capture
#print axioms memory_address_latched_after_request
#print axioms memory_address_latched_hold
theorem memory_address_stable_while_incomplete_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (incomplete : v11702 (run initial inputs (t + 1)) (inputs (t + 1)) ≠ 1) :
    v11612 (run initial inputs (t + 2)) (inputs (t + 2)) =
      v11612 (run initial inputs (t + 1)) (inputs (t + 1)) := by
  have hold : v24283 (run initial inputs (t + 1)) (inputs (t + 1)) ≠ 1 := by
    intro capture
    exact incomplete (execute_capture_replaces_only_completed _ _ valid capture)
  exact lsu_address_hold_without_capture _ _ _
    (original_assumptions_lsu_idle_run initial inputs reset environment t)
    (original_assumptions_lsu_idle_run initial inputs reset environment (t + 1)) hold
#print axioms memory_address_stable_while_incomplete_run
end NutShellProofs
