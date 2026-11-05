import Proofs.MemoryCompletion
namespace NutShellProofs
open nNutCore

theorem memory_request_has_no_alignment_fault (s : State) (i : Inputs)
    (request : v12570 s i = 1) : v11639 s i = 0 ∧ v11640 s i = 0 := by
  rcases BitVec.eq_zero_or_eq_one (v11631 s i) with a | a <;>
    rcases BitVec.eq_zero_or_eq_one (v11637 s i) with b | b
  all_goals simp [v12570, v12569, v12263, v12262, v12260, v12259, v12261, v24, a, b] at request
  simp [v11639, v11632, v11638, v11640, a, b]

theorem memory_request_requires_inner_idle (s : State) (i : Inputs)
    (request : v12570 s i = 1) :
    s.g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 0 := by
  by_cases idle : s.g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 0
  · exact idle
  · change s.g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate ≠ (0#2) at idle
    simp [v12570, v12569, v12263, v12262, v12260, v12258, v12257, v4079, idle] at request

theorem memory_request_prevents_execute_capture (s : State) (i : Inputs)
    (operation : MemoryOp) (op : v28 s i = operation.control)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (unit : v3 s i = 1) (valid : v6 s i = 1)
    (request : v12570 s i = 1) : v24283 s i ≠ 1 := by
  obtain ⟨noFault, aligned⟩ := memory_request_has_no_alignment_fault s i request
  have incomplete := memory_idle_without_fault_cannot_complete s i operation op outer
    (memory_request_requires_inner_idle s i request) noFault aligned
  intro capture
  have complete := execute_capture_replaces_only_completed s i valid capture
  simp [v11702, v11701, v11700, v11495, v11494, unit, v11699,
    v11518, v11517, incomplete] at complete
#print axioms memory_request_has_no_alignment_fault
#print axioms memory_request_requires_inner_idle
#print axioms memory_request_prevents_execute_capture
theorem memory_request_latches_address_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp)
    (currentReset : (inputs (t + 1)).g0.nreset = 0)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (request : v12570 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    MemoryAddressLatched (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have outer := original_assumptions_lsu_idle_run initial inputs reset environment t
  have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
  exact memory_address_latched_after_request _ _ _ currentReset unit request outer
    (original_assumptions_lsu_idle_run initial inputs reset environment (t + 1))
    (memory_request_prevents_execute_capture _ _ operation op outer unit valid request)
#print axioms memory_request_latches_address_run
end NutShellProofs
