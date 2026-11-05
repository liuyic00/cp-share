import Proofs.MemoryBusyHold
namespace NutShellProofs
open nNutCore

theorem memory_request_requires_execute_request (s : State) (i : Inputs)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (request : v12570 s i = 1) : v11525 s i = 1 := by
  rcases BitVec.eq_zero_or_eq_one (v11525 s i) with inactive | active
  · simp [v12570, v12569, v12263, v12262, v12260, v12258,
      v11546, v11545, v11519, outer, v2687, v11530, inactive] at request
  · exact active

theorem memory_request_execute_controls (s : State) (i : Inputs)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (request : v12570 s i = 1) :
    v3 s i = 1 ∧ v6 s i = 1 ∧ v23 s i = 0 := by
  have issued := memory_request_requires_execute_request s i outer request
  obtain ⟨unit, valid⟩ := lsu_request_controls s i issued
  refine ⟨unit, valid, ?_⟩
  rcases BitVec.eq_zero_or_eq_one (v23 s i) with zero | one
  · exact zero
  · simp [v11525, v11524, v11523, v24, one] at issued

theorem memory_request_controls_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (request : v12570 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 ∧
    v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 ∧
    v23 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := by
  exact memory_request_execute_controls _ _
    (original_assumptions_lsu_idle_run initial inputs reset environment t) request
#print axioms memory_request_requires_execute_request
#print axioms memory_request_execute_controls
#print axioms memory_request_controls_run
theorem memory_request_latches_from_decode_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp)
    (currentReset : (inputs (t + 1)).g0.nreset = 0)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (request : v12570 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    MemoryAddressLatched (run initial inputs (t + 2)) (inputs (t + 2)) := by
  obtain ⟨unit, valid, _⟩ := memory_request_controls_run initial inputs reset environment t request
  exact memory_request_latches_address_run initial inputs reset environment t operation
    currentReset valid unit matched request
#print axioms memory_request_latches_from_decode_run
end NutShellProofs
