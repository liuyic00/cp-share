import Proofs.ReferenceStoreOperands
namespace NutShellProofs
open nNutCore

theorem store_operand_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : MemoryOp)
    (store : operation.isLoad = false)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    v12150 (run initial inputs (t + 1)) (inputs (t + 1)) =
      v15394 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨_, _, kind2, _, _⟩ := (memory_decode_run initial inputs reset t).2 valid operation matched unit
  simp only [store, Bool.false_eq_true, ↓reduceIte] at kind2
  exact execute_register_operand_2_reference _ _ _
    (register_operand_2_run initial inputs reset t)
    (source2_decode_run initial inputs reset t).2 commit kind2 aligned
    (reference_zero_run initial inputs reset (t + 1))
    (committed_reference_store_uses_rs2 _ _ _ operation store commit matched)
#print axioms store_operand_matches_reference_run
end NutShellProofs
