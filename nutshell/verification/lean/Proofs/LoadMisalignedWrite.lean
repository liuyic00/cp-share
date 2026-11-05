import Proofs.LoadWriteEnable
import Proofs.MemoryMisalignment
namespace NutShellProofs
open nNutCore

theorem faulting_lsu_next_writeback_disabled (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 1)
    (fault : v11632 s i = 1 ∨ v11638 s i = 1) :
    v11462 (step s i) next = 0 := by
  have valid := commit_requires_execute_valid s i next commit
  have flush := commit_requires_unflushed s i next commit
  have active : v11524 s i = 1 := by
    simp [v11524, v11523, v11522, v11521, v11520, unit, valid, flush, v24]
  have emitted : v25485 s i = 0 := by
    rcases fault with loadFault | storeFault <;>
      simp [v25485, v25484, v25480, v25479, v25478, active,
        v25477, v25475, v25474, v25476, v24, *]
  have nextWen : v11459 (step s i) next = 0 :=
    (capture_decode_ctrl_rfWen s i next commit).trans emitted
  simp [v11462, v11461, v11460, nextWen]

theorem misaligned_memory_writeback_disabled_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (operation : MemoryOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (misaligned : v11628 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    v11462 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
  have enabled := committed_normal_memory_enabled _ _ _ operation op
    (original_assumptions_lsu_idle_run initial inputs reset environment t) unit commit
  exact faulting_lsu_next_writeback_disabled _ _ _ commit unit
    (enabled_misalignment_fault _ _ enabled misaligned)
#print axioms faulting_lsu_next_writeback_disabled
#print axioms misaligned_memory_writeback_disabled_run
end NutShellProofs
