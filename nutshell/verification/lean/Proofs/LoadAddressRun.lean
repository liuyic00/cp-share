import Proofs.MemoryBusyRun
import Proofs.LoadAddressTask
namespace NutShellProofs
open nNutCore

theorem completed_memory_address_latched_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (noFault : v11639 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (aligned : v11640 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    MemoryAddressLatched (run initial inputs (t + 1)) (inputs (t + 1)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨operation, _, op⟩ := original_assumptions_lsu_memory_run initial inputs reset environment t valid unit
  have complete := lsu_commit_requires_completion _ _ _ unit commit
  have busy : (run initial inputs (t + 1)).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate ≠ 0 := by
    intro idle
    have zero := memory_idle_without_fault_cannot_complete _ _ operation op
      (original_assumptions_lsu_idle_run initial inputs reset environment t) idle noFault aligned
    rw [zero] at complete
    contradiction
  exact (original_assumptions_memory_busy_run initial inputs reset environment t busy).latched

theorem load_address_task4_aligned_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp) (load : operation.isLoad = true)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (aligned : v11628 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    TaskHolds 4 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  obtain ⟨noFault, noFault'⟩ := memory_raw_alignment_excludes_fault _ _ aligned
  exact load_address_task4_from_latch_run initial inputs reset environment t operation load
    commit unit matched registers
    (completed_memory_address_latched_run initial inputs reset environment t commit unit noFault noFault')
#print axioms completed_memory_address_latched_run
#print axioms load_address_task4_aligned_run
end NutShellProofs
