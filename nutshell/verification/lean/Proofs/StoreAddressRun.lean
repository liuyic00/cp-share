import Proofs.MemoryMisalignment
import Proofs.StoreAddressCorrespondence
import Proofs.StoreAlignmentCorrespondence
namespace NutShellProofs
open nNutCore
theorem committed_fault_disables_store_valid (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1)
    (fault : v11632 s i = 1 ∨ v11638 s i = 1) : v31215 (step s i) next = 0 := by
  have raised := lsu_fault_raises_exception s i fault
  have valid := commit_requires_execute_valid s i next commit
  have flush := commit_requires_unflushed s i next commit
  have reset := (next_commit_controls s i next commit).1
  have active : v13724 s i = 1 := by
    simp [v13724, v13723, v13722, valid, flush, v24]
  have trapped : v30821 (step s i) next = 1 := by
    change v14430 s i = 1
    rcases BitVec.eq_zero_or_eq_one (v13720 s i) with a | a <;>
      simp [v14430, v13172, v12103, v11455, reset, v14429, v14427, v14428,
        raised, active, a]
  simp [v31215, v31214, v31213, v31212, v31211, trapped, v110]
theorem store_address_task7_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp) (store : operation.isLoad = false)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    TaskHolds 7 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
  rcases BitVec.eq_zero_or_eq_one (v11628 (run initial inputs (t + 1)) (inputs (t + 1))) with misaligned | aligned
  · have enabled := committed_normal_memory_enabled _ _ _ operation op
      (original_assumptions_lsu_idle_run initial inputs reset environment t) unit commit
    have dut := committed_fault_disables_store_valid _ _ _ commit
      (enabled_misalignment_fault _ _ enabled misaligned)
    change v31215 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 at dut
    have refValid := store_alignment_matches_reference_valid_run initial inputs reset environment t
      operation store commit unit matched registers
    have refZero := refValid.symm.trans misaligned
    change decide (v31235 (run initial inputs (t + 2)) (inputs (t + 2)) ≠ 1 ∨
      v31232 (run initial inputs (t + 2)) (inputs (t + 2)) = 1) = true
    simp [v31235, v31233, dut, refZero]
  · obtain ⟨noFault, noFault'⟩ := memory_raw_alignment_excludes_fault _ _ aligned
    have latched := completed_memory_address_latched_run initial inputs reset environment t commit unit noFault noFault'
    have address := (committed_latched_checker_address _ _ _ commit unit latched).trans
      ((sign_extend_address_low39 _ (original_memory_address_upper_zero _ _
        (environment (t + 1)) (next_commit_controls _ _ _ commit).1)).trans
        (store_address_matches_reference_node_run initial inputs reset environment t operation store commit unit matched registers))
    change v31229 (run initial inputs (t + 2)) (inputs (t + 2)) =
      v24024 (run initial inputs (t + 2)) (inputs (t + 2)) at address
    change decide (v31235 (run initial inputs (t + 2)) (inputs (t + 2)) ≠ 1 ∨
      v31232 (run initial inputs (t + 2)) (inputs (t + 2)) = 1) = true
    simp [v31232, v31231, v31230, address]
#print axioms committed_fault_disables_store_valid
#print axioms store_address_task7_run
end NutShellProofs
