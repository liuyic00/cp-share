import Proofs.MemoryNoTrap
import Proofs.MemorySizeTasks
namespace NutShellProofs
open nNutCore

theorem no_trap_next_checker_trap_zero (s : State) (i next : Inputs)
    (clear : v13725 s i = 0) : v30821 (step s i) next = 0 := by
  change v14430 s i = 0
  rcases BitVec.eq_zero_or_eq_one (v13720 s i) with a | a <;>
    rcases BitVec.eq_zero_or_eq_one (v13684 s i) with b | b <;>
    rcases BitVec.eq_zero_or_eq_one (v13724 s i) with c | c <;>
    simp [v13725, v13721, a, b, c] at clear <;>
    simp [v14430, v14429, v14427, v14428, a, b, c, v24]

theorem memory_size_nonzero (operation : MemoryOp) : operation.sizeBits ≠ 0 := by
  cases operation <;> decide

theorem aligned_load_event_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp) (direction : operation.isLoad = true)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (aligned : v11628 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    v31121 (run initial inputs (t + 2)) (inputs (t + 2)) = 1 := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have trap := no_trap_next_checker_trap_zero _ _ (inputs (t + 2))
    (aligned_memory_no_trap_run initial inputs reset t operation valid unit matched aligned)
  change v30821 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 at trap
  have size := completed_load_size_run initial inputs reset environment t operation direction commit unit matched aligned
  have nonzero : v30865 (run initial inputs (t + 2)) (inputs (t + 2)) ≠ 0 := by
    intro zero
    have empty := load_checker_size_mask_0 _ _ zero
    exact memory_size_nonzero operation (size.symm.trans empty)
  have positive : 0 < (v30865 (run initial inputs (t + 2)) (inputs (t + 2))).toNat := by
    have bound := (v30865 (run initial inputs (t + 2)) (inputs (t + 2))).isLt
    have neq : (v30865 (run initial inputs (t + 2)) (inputs (t + 2))).toNat ≠ 0 := by
      intro zero
      exact nonzero (BitVec.eq_of_toNat_eq (by simpa using zero))
    omega
  simp [v31121, v31120, v31119, v31118, v31116, v31115, v31114, v31117, v30709, v30708, v30707, commit, trap, v110, positive]
#print axioms aligned_load_event_run

theorem aligned_store_event_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp) (direction : operation.isLoad = false)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (aligned : v11628 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    v31215 (run initial inputs (t + 2)) (inputs (t + 2)) = 1 := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have trap := no_trap_next_checker_trap_zero _ _ (inputs (t + 2))
    (aligned_memory_no_trap_run initial inputs reset t operation valid unit matched aligned)
  change v30821 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 at trap
  have size := completed_store_size_run initial inputs reset environment t operation direction commit unit matched aligned
  have nonzero : v30869 (run initial inputs (t + 2)) (inputs (t + 2)) ≠ 0 := by
    intro zero
    have empty := store_checker_size_mask_0 _ _ zero
    exact memory_size_nonzero operation (size.symm.trans empty)
  have positive : 0 < (v30869 (run initial inputs (t + 2)) (inputs (t + 2))).toNat := by
    have bound := (v30869 (run initial inputs (t + 2)) (inputs (t + 2))).isLt
    have neq : (v30869 (run initial inputs (t + 2)) (inputs (t + 2))).toNat ≠ 0 := by
      intro zero
      exact nonzero (BitVec.eq_of_toNat_eq (by simpa using zero))
    omega
  simp [v31215, v31214, v31213, v31212, v31210, v31209, v31208, v31211, v30709, v30708, v30707, commit, trap, v110, positive]
#print axioms aligned_store_event_run
#print axioms no_trap_next_checker_trap_zero
end NutShellProofs
