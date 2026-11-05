import Proofs.MemoryRequestControls
namespace NutShellProofs
open nNutCore

theorem memory_request_preserves_execute_identity (s : State) (i next : Inputs)
    (operation : MemoryOp) (op : v28 s i = operation.control)
    (reset : i.g0.nreset = 0)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (request : v12570 s i = 1) :
    EXUPending (step s i) = some (EXUPair s) ∧ v3 (step s i) next = 1 := by
  obtain ⟨unit, valid, noFlush⟩ := memory_request_execute_controls s i outer request
  obtain ⟨noFault, aligned⟩ := memory_request_has_no_alignment_fault s i request
  have incomplete := memory_idle_without_fault_cannot_complete s i operation op outer
    (memory_request_requires_inner_idle s i request) noFault aligned
  have hold := memory_request_prevents_execute_capture s i operation op outer unit valid request
  have noComplete : v11702 s i ≠ 1 := by
    simp [v11702, v11701, v11700, v11495, v11494, unit, v11699,
      v11518, v11517, incomplete]
  have flush : v24276 s i = 0 := by
    rcases BitVec.eq_zero_or_eq_one (v14 s i) with clear | active
    · simp [v24276, v21, v20, v19, v18, v17, v16, clear]
    · simp [v23, v22, v21, v20, v19, v18, v17, v15, active] at noFlush
  constructor
  · rw [execute_pending_step s i reset flush, if_neg hold, if_neg noComplete]
    exact if_pos valid
  · change v24913 s i = 1
    simpa only [v24913, hold, ↓reduceIte] using unit
#print axioms memory_request_preserves_execute_identity
theorem memory_request_entry_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp)
    (currentReset : (inputs (t + 1)).g0.nreset = 0)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (request : v12570 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    EXUPending (run initial inputs (t + 2)) = some (EXUPair (run initial inputs (t + 1))) ∧
    v3 (run initial inputs (t + 2)) (inputs (t + 2)) = 1 ∧
    MemoryAddressLatched (run initial inputs (t + 2)) (inputs (t + 2)) := by
  obtain ⟨unit, valid, _⟩ := memory_request_controls_run initial inputs reset environment t request
  have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
  have identity := memory_request_preserves_execute_identity _ _ (inputs (t + 2)) operation op currentReset
    (original_assumptions_lsu_idle_run initial inputs reset environment t) request
  exact ⟨identity.1, identity.2,
    memory_request_latches_from_decode_run initial inputs reset environment t operation currentReset matched request⟩
#print axioms memory_request_entry_run
end NutShellProofs
