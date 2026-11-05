import Proofs.MemoryEventValid
namespace NutShellProofs
open nNutCore
theorem load_valid_task3_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp) (direction : operation.isLoad = true)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    TaskHolds 3 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have reference := load_alignment_matches_reference_valid_run initial inputs reset environment t operation direction commit unit matched registers
  have equal : v31121 (run initial inputs (t + 2)) (inputs (t + 2)) = v31135 (run initial inputs (t + 2)) (inputs (t + 2)) := by
    rcases BitVec.eq_zero_or_eq_one (v11628 (run initial inputs (t + 1)) (inputs (t + 1))) with misaligned | aligned
    · have valid := commit_requires_execute_valid _ _ _ commit
      have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
      have enabled := committed_normal_memory_enabled _ _ _ operation op
        (original_assumptions_lsu_idle_run initial inputs reset environment t) unit commit
      have zero := committed_fault_disables_load_valid _ _ _ commit (enabled_misalignment_fault _ _ enabled misaligned)
      exact zero.trans (reference.symm.trans misaligned).symm
    · exact (aligned_load_event_run initial inputs reset environment t operation direction commit unit matched aligned).trans
        (reference.symm.trans aligned).symm
  change decide (v31137 (run initial inputs (t + 2)) (inputs (t + 2)) ≠ 1 ∨
    v31136 (run initial inputs (t + 2)) (inputs (t + 2)) = 1) = true
  simp [v31136, equal]
#print axioms load_valid_task3_run
theorem store_valid_task6_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp) (direction : operation.isLoad = false)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    TaskHolds 6 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have reference := store_alignment_matches_reference_valid_run initial inputs reset environment t operation direction commit unit matched registers
  have equal : v31215 (run initial inputs (t + 2)) (inputs (t + 2)) = v31224 (run initial inputs (t + 2)) (inputs (t + 2)) := by
    rcases BitVec.eq_zero_or_eq_one (v11628 (run initial inputs (t + 1)) (inputs (t + 1))) with misaligned | aligned
    · have valid := commit_requires_execute_valid _ _ _ commit
      have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
      have enabled := committed_normal_memory_enabled _ _ _ operation op
        (original_assumptions_lsu_idle_run initial inputs reset environment t) unit commit
      have zero := committed_fault_disables_store_valid _ _ _ commit (enabled_misalignment_fault _ _ enabled misaligned)
      exact zero.trans (reference.symm.trans misaligned).symm
    · exact (aligned_store_event_run initial inputs reset environment t operation direction commit unit matched aligned).trans
        (reference.symm.trans aligned).symm
  change decide (v31226 (run initial inputs (t + 2)) (inputs (t + 2)) ≠ 1 ∨
    v31225 (run initial inputs (t + 2)) (inputs (t + 2)) = 1) = true
  simp [v31225, equal]
#print axioms store_valid_task6_run
end NutShellProofs
