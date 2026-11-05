import Proofs.StoreDataRun
namespace NutShellProofs
open nNutCore
theorem completed_store_data_latched_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (noFault : v11639 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (aligned : v11640 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    StoreDataLatched (run initial inputs (t + 1)) (inputs (t + 1)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨operation, _, op⟩ := original_assumptions_lsu_memory_run initial inputs reset environment t valid unit
  have complete := lsu_commit_requires_completion _ _ _ unit commit
  have busy : (run initial inputs (t + 1)).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate ≠ 0 := by
    intro idle
    have zero := memory_idle_without_fault_cannot_complete _ _ operation op
      (original_assumptions_lsu_idle_run initial inputs reset environment t) idle noFault aligned
    rw [zero] at complete
    contradiction
  exact original_assumptions_busy_store_data_run initial inputs reset environment t busy

theorem completed_checker_store_data_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (aligned : v11628 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    v30873 (run initial inputs (t + 2)) (inputs (t + 2)) =
      v14539 (run initial inputs (t + 1)) (inputs (t + 1)) := by
  obtain ⟨noFault, noFault'⟩ := memory_raw_alignment_excludes_fault _ _ aligned
  have latched := completed_store_data_latched_run initial inputs reset environment t commit unit noFault noFault'
  change (run initial inputs (t + 1)).g44.r1436_nbackend_5Fexu_5Fmem_5Frvfi_5Freg_5Fwdata = _ at latched
  change v30873 (step (run initial inputs (t + 1)) (inputs (t + 1))) (inputs (t + 2)) = _
  rw [committed_store_data_is_latch _ _ _ commit unit,
    store_data_latch_step _ _ (next_commit_controls _ _ _ commit).1 unit, latched]
  simp only [ite_self]
#print axioms completed_store_data_latched_run
#print axioms completed_checker_store_data_run
end NutShellProofs
