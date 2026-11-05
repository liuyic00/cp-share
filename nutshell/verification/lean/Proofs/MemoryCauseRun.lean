import Proofs.MemoryFaultDirection
import Proofs.MemoryCauseSources
import Proofs.MemoryNoTrap
namespace NutShellProofs
open nNutCore

/-- The DUT cause selector agrees with decoded load/store alignment semantics. -/
theorem memory_cause_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (operation : MemoryOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1) :
    v13780 (run initial inputs (t + 1)) (inputs (t + 1)) =
      if v11628 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 then 0
      else (if operation.isLoad then 4 else 6) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
  have outer := original_assumptions_lsu_idle_run initial inputs reset environment t
  have enabled := committed_normal_memory_enabled _ _ _ operation op outer unit commit
  have faults := normal_memory_fault_direction _ _ operation op outer enabled
  have illegal := (memory_legal_run initial inputs reset t).2 valid operation matched unit
  rw [memory_cause_remaining_sources_run initial inputs reset t valid unit illegal, faults.1, faults.2]
  cases operation <;>
    rcases BitVec.eq_zero_or_eq_one (v11628 (run initial inputs (t + 1)) (inputs (t + 1))) with alignment | alignment <;>
    simp [alignment, MemoryOp.isLoad]
#print axioms memory_cause_run
end NutShellProofs
