import Proofs.MemoryReferenceExceptionRun
import Proofs.MemoryMisalignment
import Proofs.MemoryNoTrap
import Proofs.TrapEventCorrespondence
namespace NutShellProofs
open nNutCore

theorem committed_fault_raises_trap (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1)
    (fault : v11632 s i = 1 ∨ v11638 s i = 1) : v13725 s i = 1 := by
  have raised := lsu_fault_raises_exception s i fault
  have valid := commit_requires_execute_valid s i next commit
  have flush := commit_requires_unflushed s i next commit
  have active : v13724 s i = 1 := by
    simp [v13724, v13723, v13722, valid, flush, v24]
  rcases BitVec.eq_zero_or_eq_one (v13720 s i) with interrupt | interrupt <;>
    simp [v13725, v13721, raised, active, interrupt]

theorem committed_memory_trap_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (operation : MemoryOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    v13725 (run initial inputs (t + 1)) (inputs (t + 1)) =
      v23407 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  rw [reference_memory_exception_run initial inputs reset environment t operation commit unit matched registers]
  have valid := commit_requires_execute_valid _ _ _ commit
  rcases BitVec.eq_zero_or_eq_one (v11628 (run initial inputs (t + 1)) (inputs (t + 1))) with misaligned | aligned
  · have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
    have enabled := committed_normal_memory_enabled _ _ _ operation op
      (original_assumptions_lsu_idle_run initial inputs reset environment t) unit commit
    have trap := committed_fault_raises_trap _ _ _ commit (enabled_misalignment_fault _ _ enabled misaligned)
    simpa [misaligned] using trap
  · simpa [aligned] using aligned_memory_no_trap_run initial inputs reset t operation valid unit matched aligned

theorem committed_lsu_event_task43_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    TaskHolds 43 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨operation, matched, _⟩ := original_assumptions_lsu_memory_run initial inputs reset environment t valid unit
  have trap := committed_memory_trap_matches_reference_run initial inputs reset environment t operation commit unit matched registers
  have actual := captured_event_is_trap (run initial inputs (t + 1)) (inputs (t + 1)) (inputs (t + 2)) (next_commit_controls _ _ _ commit).1
  change v31736 (run initial inputs (t + 2)) (inputs (t + 2)) = _ at actual
  have flags : v31736 (run initial inputs (t + 2)) (inputs (t + 2)) =
      v31739 (run initial inputs (t + 2)) (inputs (t + 2)) := by
    rw [actual, trap]
    simp [v31739, v31738, v31737, v14560, v14559, v14558, commit]
  change decide (_ ≠ 1 ∨ v31740 (run initial inputs (t + 2)) (inputs (t + 2)) = 1) = true
  simp [v31740, flags]
#print axioms committed_fault_raises_trap
#print axioms committed_memory_trap_matches_reference_run
#print axioms committed_lsu_event_task43_run
end NutShellProofs
