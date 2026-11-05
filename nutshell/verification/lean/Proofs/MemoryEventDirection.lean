import Proofs.MemorySizeTasks
namespace NutShellProofs
open nNutCore
theorem committed_load_has_no_store_event_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp) (direction : operation.isLoad = true)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1) :
    v31215 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
  have outer := original_assumptions_lsu_idle_run initial inputs reset environment t
  have enabled := committed_normal_memory_enabled _ _ _ operation op outer unit commit
  rcases BitVec.eq_zero_or_eq_one (v11628 (run initial inputs (t + 1)) (inputs (t + 1))) with misaligned | aligned
  · exact committed_fault_disables_store_valid _ _ _ commit (enabled_misalignment_fault _ _ enabled misaligned)
  · have routing := normal_memory_mask_direction _ _ operation op outer enabled
    have masks := completed_memory_checker_masks_run initial inputs reset environment t commit unit aligned
    have zero : v30869 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 :=
      masks.2.trans (by simpa only [direction, Bool.true_eq, ↓reduceIte] using routing.2)
    simp [v31215, v31214, v31213, v31212, v31210, v31209, v31208, zero]
#print axioms committed_load_has_no_store_event_run
theorem committed_store_has_no_load_event_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp) (direction : operation.isLoad = false)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1) :
    v31121 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
  have outer := original_assumptions_lsu_idle_run initial inputs reset environment t
  have enabled := committed_normal_memory_enabled _ _ _ operation op outer unit commit
  rcases BitVec.eq_zero_or_eq_one (v11628 (run initial inputs (t + 1)) (inputs (t + 1))) with misaligned | aligned
  · exact committed_fault_disables_load_valid _ _ _ commit (enabled_misalignment_fault _ _ enabled misaligned)
  · have routing := normal_memory_mask_direction _ _ operation op outer enabled
    have masks := completed_memory_checker_masks_run initial inputs reset environment t commit unit aligned
    have zero : v30865 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 :=
      masks.1.trans (by simpa only [direction, Bool.true_eq, ↓reduceIte] using routing.1)
    simp [v31121, v31120, v31119, v31118, v31116, v31115, v31114, zero]
#print axioms committed_store_has_no_load_event_run
end NutShellProofs
