import Proofs.MemoryCompletionState
namespace NutShellProofs
open nNutCore

theorem committed_latched_checker_address (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 1)
    (latched : MemoryAddressLatched s i) :
    v31144 (step s i) next =
      (BitVec.extractLsb' 0 39 (v11612 s i)).signExtend 64 := by
  rw [checker_memory_address_extension, committed_memory_address_is_latch s i next commit unit,
    memory_address_latch_step s i (next_commit_controls s i next commit).1 unit]
  unfold MemoryAddressLatched at latched
  rw [latched]
  simp only [ite_self,
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 39 ≤ 39),
    BitVec.extractLsb'_eq_self]

theorem load_address_task4_from_latch_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp) (load : operation.isLoad = true)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (latched : MemoryAddressLatched (run initial inputs (t + 1)) (inputs (t + 1))) :
    TaskHolds 4 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have address := (committed_latched_checker_address _ _ _ commit unit latched).trans
    (load_address_extended_matches_reference_run initial inputs reset environment t operation load commit unit matched aligned)
  change decide (v31150 (run initial inputs (t + 2)) (inputs (t + 2)) ≠ 1 ∨
    v31147 (run initial inputs (t + 2)) (inputs (t + 2)) = 1) = true
  have eq : v31144 (run initial inputs (t + 2)) (inputs (t + 2)) =
      v24059 (run initial inputs (t + 2)) (inputs (t + 2)) := address
  simp [v31147, v31146, v31145, eq]
#print axioms committed_latched_checker_address
#print axioms load_address_task4_from_latch_run
end NutShellProofs
