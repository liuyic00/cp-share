import Proofs.MemoryCauseRun
import Proofs.MemoryReferenceCauseRun
namespace NutShellProofs
open nNutCore

/-- The recorded cause is the zero-extended selected cause for an active exception. -/
theorem captured_exception_cause (s : State) (i next : Inputs)
    (active : v13724 s i = 1) (raised : v13684 s i = 1) :
    v31758 (step s i) next = (v13780 s i).setWidth 64 := by
  change (v13727 (step s i) next ++ v14419 s i) = _
  simp only [v14419, v14417, active, raised, v13727]
  simpa using (BitVec.setWidth_eq_append (x := v13780 s i) (w := 64) (by omega)).symm

/-- A zero cause remains zero regardless of the exception gate. -/
theorem captured_zero_exception_cause (s : State) (i next : Inputs)
    (cause : v13780 s i = 0) : v31758 (step s i) next = 0 := by
  change (v13727 (step s i) next ++ v14419 s i) = 0
  simp [v13727, v14419, v14418, cause]

/-- Actual recorded LSU cause, including aligned operations and both fault directions. -/
theorem recorded_memory_cause_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (operation : MemoryOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1) :
    v31758 (run initial inputs (t + 2)) (inputs (t + 2)) =
      if v11628 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 then 0
      else (if operation.isLoad then 4 else 6) := by
  have cause := memory_cause_run initial inputs reset environment t operation commit unit matched
  rcases BitVec.eq_zero_or_eq_one (v11628 (run initial inputs (t + 1)) (inputs (t + 1))) with alignment | alignment
  · have valid := commit_requires_execute_valid _ _ _ commit
    have flush := commit_requires_unflushed _ _ _ commit
    have active : v13724 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 := by
      simp [v13724, v13723, v13722, valid, flush, v24]
    have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
    have enabled := committed_normal_memory_enabled _ _ _ operation op
      (original_assumptions_lsu_idle_run initial inputs reset environment t) unit commit
    have raised := lsu_fault_raises_exception _ _ (enabled_misalignment_fault _ _ enabled alignment)
    have captured := captured_exception_cause _ _ (inputs (t + 2)) active raised
    change v31758 (run initial inputs (t + 2)) (inputs (t + 2)) = _ at captured
    rw [captured, cause]
    cases operation <;> simp [alignment, MemoryOp.isLoad]
  · have zero : v13780 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := by
      simpa [alignment] using cause
    simpa [alignment] using captured_zero_exception_cause _ _ (inputs (t + 2)) zero

/-- Original cause-equality assertion for every committed LSU operation. -/
theorem committed_lsu_event_task45_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    TaskHolds 45 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨operation, matched, _⟩ := original_assumptions_lsu_memory_run initial inputs reset environment t valid unit
  have same := (recorded_memory_cause_run initial inputs reset environment t operation commit unit matched).trans
    (reference_memory_cause_run initial inputs reset environment t operation commit unit matched registers).symm
  change decide (_ ≠ 1 ∨ v31764 (run initial inputs (t + 2)) (inputs (t + 2)) = 1) = true
  simp [v31764, same]
#print axioms captured_exception_cause
#print axioms captured_zero_exception_cause
#print axioms recorded_memory_cause_run
#print axioms committed_lsu_event_task45_run
end NutShellProofs
