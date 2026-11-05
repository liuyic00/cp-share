import Proofs.MemoryLegalPipeline
import Proofs.MemoryExceptionSources
import Proofs.MemoryAlignmentHold
namespace NutShellProofs
open nNutCore

theorem aligned_memory_no_trap_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : MemoryOp)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (aligned : v11628 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    v13725 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := by
  have illegal := (memory_legal_run initial inputs reset t).2 valid operation matched unit
  have loadFault : v11632 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := by
    simp [v11632, v11631, v11630, v11629, aligned, v24]
  have storeFault : v11638 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := by
    simp [v11638, v11637, v11636, v11635, aligned, v24]
  exact memory_no_trap_remaining_sources_run initial inputs reset t valid unit illegal loadFault storeFault

#print axioms aligned_memory_no_trap_run
end NutShellProofs
