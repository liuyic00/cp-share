import Proofs.MemoryCompletedMasks
import Proofs.ShiftedMaskSize
import Proofs.MemoryMisalignment
namespace NutShellProofs
open nNutCore
theorem completed_load_size_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp) (direction : operation.isLoad = true)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (aligned : v11628 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    v31183 (run initial inputs (t + 2)) (inputs (t + 2)) = operation.sizeBits := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
  have outer := original_assumptions_lsu_idle_run initial inputs reset environment t
  have enabled := committed_normal_memory_enabled _ _ _ operation op outer unit commit
  have routing := normal_memory_mask_direction _ _ operation op outer enabled
  have masks := completed_memory_checker_masks_run initial inputs reset environment t commit unit aligned
  apply shifted_load_mask_size _ _ _ _ operation op outer aligned
  exact masks.1.trans (by simpa only [direction, Bool.true_eq, ↓reduceIte] using routing.1)
#print axioms completed_load_size_run
theorem completed_store_size_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp) (direction : operation.isLoad = false)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (aligned : v11628 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    v31337 (run initial inputs (t + 2)) (inputs (t + 2)) = operation.sizeBits := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
  have outer := original_assumptions_lsu_idle_run initial inputs reset environment t
  have enabled := committed_normal_memory_enabled _ _ _ operation op outer unit commit
  have routing := normal_memory_mask_direction _ _ operation op outer enabled
  have masks := completed_memory_checker_masks_run initial inputs reset environment t commit unit aligned
  apply shifted_store_mask_size _ _ _ _ operation op outer aligned
  exact masks.2.trans (by simpa only [direction, Bool.true_eq, ↓reduceIte] using routing.2)
#print axioms completed_store_size_run
end NutShellProofs
