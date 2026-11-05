import Proofs.NonCSRPipeline
import Proofs.NonLSUMemoryTasks
namespace NutShellProofs
open nNutCore

theorem temporary_pc32_execute_noncsr (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    v3 (run initial inputs (t + 1)) (inputs (t + 1)) ≠ 3 := by
  exact (noncsr_decode_run initial inputs reset
    (temporary_pc32_active_decode_noncsr initial inputs reset environment restriction) t).2 valid

/-- Original memory tasks for all execution-unit branches, under the explicit temporary
PC restriction and the still-outstanding architectural register correspondence. -/
theorem temporary_pc32_memory_tasks_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    ∀ task : Fin 48, 3 ≤ task.val → task.val ≤ 9 →
      TaskHolds task (run initial inputs (t + 2)) (inputs (t + 2)) := by
  apply non_csr_memory_tasks_run initial inputs reset environment t _ registers
  intro commit
  exact temporary_pc32_execute_noncsr initial inputs reset environment restriction t
    (commit_requires_execute_valid _ _ _ commit)
#print axioms temporary_pc32_execute_noncsr
#print axioms temporary_pc32_memory_tasks_run
end NutShellProofs
