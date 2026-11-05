import Proofs.MemoryMaskRun
namespace NutShellProofs
open nNutCore
theorem completed_memory_masks_latched_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (noFault : v11639 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (aligned : v11640 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    MemoryMasksLatched (run initial inputs (t + 1)) (inputs (t + 1)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨operation, _, op⟩ := original_assumptions_lsu_memory_run initial inputs reset environment t valid unit
  have complete := lsu_commit_requires_completion _ _ _ unit commit
  have busy : (run initial inputs (t + 1)).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate ≠ 0 := by
    intro idle
    have zero := memory_idle_without_fault_cannot_complete _ _ operation op
      (original_assumptions_lsu_idle_run initial inputs reset environment t) idle noFault aligned
    rw [zero] at complete
    contradiction
  exact original_assumptions_busy_masks_run initial inputs reset environment t busy

theorem committed_latched_masks (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 1)
    (latched : MemoryMasksLatched s i) :
    v30865 (step s i) next = v14482 s i ∧
    v30869 (step s i) next = v14489 s i := by
  obtain ⟨read, write⟩ := latched
  rw [committed_read_mask_is_latch s i next commit unit,
    committed_write_mask_is_latch s i next commit unit,
    memory_read_mask_latch_step s i (next_commit_controls s i next commit).1 unit,
    memory_write_mask_latch_step s i (next_commit_controls s i next commit).1 unit,
    read, write]
  simp only [ite_self, and_self]

theorem completed_memory_checker_masks_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (aligned : v11628 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    v30865 (run initial inputs (t + 2)) (inputs (t + 2)) =
      v14482 (run initial inputs (t + 1)) (inputs (t + 1)) ∧
    v30869 (run initial inputs (t + 2)) (inputs (t + 2)) =
      v14489 (run initial inputs (t + 1)) (inputs (t + 1)) := by
  obtain ⟨noFault, noFault'⟩ := memory_raw_alignment_excludes_fault _ _ aligned
  exact committed_latched_masks _ _ _ commit unit
    (completed_memory_masks_latched_run initial inputs reset environment t commit unit noFault noFault')
#print axioms completed_memory_masks_latched_run
#print axioms committed_latched_masks
#print axioms completed_memory_checker_masks_run
theorem normal_memory_mask_direction (s : State) (i : Inputs) (operation : MemoryOp)
    (op : v28 s i = operation.control)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (enabled : v11546 s i = 1) :
    v14482 s i = (if operation.isLoad then v14480 s i else 0) ∧
    v14489 s i = (if operation.isLoad then 0 else v14480 s i) := by
  cases operation <;>
    simp [v14482, v14489, v14451, v14487, v14449, v14448, v12314,
      v12313, v11571, v11570, v14450, v14486, v14481, v14488, v2687,
      enabled, v11569, v11568, v11519, outer, v11526, op,
      MemoryOp.control, MemoryOp.isLoad]
#print axioms normal_memory_mask_direction
end NutShellProofs
