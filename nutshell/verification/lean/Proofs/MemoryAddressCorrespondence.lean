import Proofs.ReferenceMemoryOperands
namespace NutShellProofs
open nNutCore
theorem memory_operand_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : MemoryOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    v11592 (run initial inputs (t + 1)) (inputs (t + 1)) =
      v15632 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨_, kind1, _, _, _⟩ := (memory_decode_run initial inputs reset t).2 valid operation matched unit
  have opcode := opcode_of_mask _ (28799 : BitVec 64) operation.encoding (by decide) matched.symm
  have notLui : BitVec.extractLsb' 0 7 (EXUPair (run initial inputs (t + 1))).1 ≠ 55 := by
    rw [opcode]
    cases operation <;> decide
  exact execute_register_operand_1_reference _ _ _
    (register_operand_1_run initial inputs reset t)
    (source1_decode_run initial inputs reset t).2 commit kind1 aligned
    (reference_zero_run initial inputs reset (t + 1))
    (committed_reference_memory_uses_rs1 _ _ _ operation commit matched) notLui

theorem memory_address_reference_operands_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    v11612 (run initial inputs (t + 1)) (inputs (t + 1)) =
      v15632 (run initial inputs (t + 2)) (inputs (t + 2)) +
      v16164 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  rw [lsu_address_sum _ _ (original_assumptions_lsu_idle_run initial inputs reset environment t),
    memory_operand_matches_reference_run initial inputs reset t operation commit unit matched aligned,
    memory_immediate_matches_reference_run initial inputs reset t operation commit unit matched]
#print axioms memory_operand_matches_reference_run
#print axioms memory_address_reference_operands_run
end NutShellProofs
