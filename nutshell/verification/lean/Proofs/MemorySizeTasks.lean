import Proofs.ReferenceMemorySizeAlignment
namespace NutShellProofs
open nNutCore
theorem load_size_task5_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp) (load : operation.isLoad = true)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    TaskHolds 5 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  rcases BitVec.eq_zero_or_eq_one (v11628 (run initial inputs (t + 1)) (inputs (t + 1))) with misaligned | aligned
  · have valid := commit_requires_execute_valid _ _ _ commit
    have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
    have enabled := committed_normal_memory_enabled _ _ _ operation op
      (original_assumptions_lsu_idle_run initial inputs reset environment t) unit commit
    have dut := committed_fault_disables_load_valid _ _ _ commit
      (enabled_misalignment_fault _ _ enabled misaligned)
    change v31121 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 at dut
    have refValid := load_alignment_matches_reference_valid_run initial inputs reset environment t
      operation load commit unit matched registers
    have refZero := refValid.symm.trans misaligned
    change decide (v31207 (run initial inputs (t + 2)) (inputs (t + 2)) ≠ 1 ∨
      v31205 (run initial inputs (t + 2)) (inputs (t + 2)) = 1) = true
    simp [v31207, v31148, dut, refZero]
  · have size := completed_load_size_run initial inputs reset environment t operation load commit unit matched aligned
    have low : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&& (28799 : BitVec 32) = operation.encoding.setWidth 32 := by
      have instruction := committed_reference_instruction _ _ _ commit
      change v14575 (run initial inputs (t + 2)) (inputs (t + 2)) =
        BitVec.extractLsb' 0 32 (EXUPair (run initial inputs (t + 1))).1 at instruction
      rw [instruction]
      exact store_match_low32 operation _ matched
    have address := memory_address_reference_operands_run initial inputs reset environment t operation commit unit matched registers
    have valid := commit_requires_execute_valid _ _ _ commit
    have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
    have alignment := normal_memory_alignment _ (inputs (t + 1)) operation op
      (original_assumptions_lsu_idle_run initial inputs reset environment t)
    rw [address] at alignment
    have refSize := reference_load_size_alignment _ _ operation load commit low
    have refEq : v31204 (run initial inputs (t + 2)) (inputs (t + 2)) = operation.sizeBits := by
      rw [aligned] at alignment
      split at alignment
      · rename_i h
        simpa only [h, ↓reduceIte] using refSize
      · contradiction
    change decide (v31207 (run initial inputs (t + 2)) (inputs (t + 2)) ≠ 1 ∨
      v31205 (run initial inputs (t + 2)) (inputs (t + 2)) = 1) = true
    simp [v31205, size, refEq]

#print axioms load_size_task5_run
theorem store_size_task9_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp) (store : operation.isLoad = false)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    TaskHolds 9 (run initial inputs (t + 2)) (inputs (t + 2)) := by
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
    change decide (v31353 (run initial inputs (t + 2)) (inputs (t + 2)) ≠ 1 ∨
      v31351 (run initial inputs (t + 2)) (inputs (t + 2)) = 1) = true
    simp [v31353, v31233, dut, refZero]
  · have size := completed_store_size_run initial inputs reset environment t operation store commit unit matched aligned
    have low : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&& (28799 : BitVec 32) = operation.encoding.setWidth 32 := by
      have instruction := committed_reference_instruction _ _ _ commit
      change v14575 (run initial inputs (t + 2)) (inputs (t + 2)) =
        BitVec.extractLsb' 0 32 (EXUPair (run initial inputs (t + 1))).1 at instruction
      rw [instruction]
      exact store_match_low32 operation _ matched
    have address := memory_address_reference_operands_run initial inputs reset environment t operation commit unit matched registers
    have valid := commit_requires_execute_valid _ _ _ commit
    have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
    have alignment := normal_memory_alignment _ (inputs (t + 1)) operation op
      (original_assumptions_lsu_idle_run initial inputs reset environment t)
    rw [address] at alignment
    have refSize := reference_store_size_alignment _ _ operation store commit low
    have refEq : v31350 (run initial inputs (t + 2)) (inputs (t + 2)) = operation.sizeBits := by
      rw [aligned] at alignment
      split at alignment
      · rename_i h
        simpa only [h, ↓reduceIte] using refSize
      · contradiction
    change decide (v31353 (run initial inputs (t + 2)) (inputs (t + 2)) ≠ 1 ∨
      v31351 (run initial inputs (t + 2)) (inputs (t + 2)) = 1) = true
    simp [v31351, size, refEq]

#print axioms store_size_task9_run
end NutShellProofs
