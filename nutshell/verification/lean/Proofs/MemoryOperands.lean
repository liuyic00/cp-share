import Proofs.MemoryAddress
import Proofs.JumpOperands
namespace NutShellProofs
open nNutCore
theorem memory_register_operand_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : MemoryOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1) :
    v11592 (run initial inputs (t + 1)) (inputs (t + 1)) =
      dutRead.v25201 (run initial inputs (t + 2)) (inputs (t + 2))
        (BitVec.extractLsb' 15 5 (EXUPair (run initial inputs (t + 1))).1) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨_, kind1, _, _, _⟩ := (memory_decode_run initial inputs reset t).2 valid operation matched unit
  obtain ⟨noReset, noFlush⟩ := next_commit_controls _ _ _ commit
  have opcode := opcode_of_mask _ (28799 : BitVec 64) operation.encoding (by decide) matched.symm
  have notLui : BitVec.extractLsb' 0 7 (EXUPair (run initial inputs (t + 1))).1 ≠ 55 := by
    rw [opcode]
    cases operation <;> decide
  have address := (source1_decode_run initial inputs reset t).2 valid kind1 (fun _ => notLui)
  have operand := register_operand_1_run initial inputs reset t
    (inputs (t + 1)) (inputs (t + 2)) valid kind1 noReset noFlush
  change v11592 (run initial inputs (t + 1)) (inputs (t + 1)) = _ at operand
  simpa only [address] using operand

#print axioms memory_register_operand_run
theorem committed_memory_address_from_register_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1) :
    v11612 (run initial inputs (t + 1)) (inputs (t + 1)) =
      dutRead.v25201 (run initial inputs (t + 2)) (inputs (t + 2))
        (BitVec.extractLsb' 15 5 (EXUPair (run initial inputs (t + 1))).1) +
      memoryImmediate operation (EXUPair (run initial inputs (t + 1))).1 := by
  have address := memory_address_run initial inputs reset environment t operation
    (commit_requires_execute_valid _ _ _ commit) unit matched
  rw [memory_register_operand_run initial inputs reset t operation commit unit matched] at address
  exact address
#print axioms committed_memory_address_from_register_run
end NutShellProofs
