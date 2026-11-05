import Proofs.TrapCommitPC
import Proofs.MemoryTrapCorrespondence
import Proofs.MemoryNoTrap
import Proofs.SequentialCommitPC
import Proofs.MemoryReferenceExceptionRun
namespace NutShellProofs
open nNutCore

theorem temporary_pc32_reference_aligned_memory_commit (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) (operation : MemoryOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (addressAligned : v11628 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (aligned : RetirementReferenceAligned (run initial inputs (t + 2))) :
    RetirementReferenceAligned (run initial inputs (t + 3)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have noTrap := aligned_memory_no_trap_run initial inputs reset t operation valid unit matched addressAligned
  have noRedirectBit := nontrapping_lsu_has_no_redirect _ _ _ commit unit noTrap
  change v8 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 at noRedirectBit
  have noRedirect : v14 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 := by
    simp [v14, v13, v12, v11, v10, noRedirectBit]
  exact temporary_pc32_reference_sequential_commit initial inputs reset environment restriction t
    currentReset commit noRedirect
    (aligned_memory_reference_pc_run initial inputs reset environment t operation commit unit matched
      registers addressAligned currentReset) aligned

#print axioms temporary_pc32_reference_aligned_memory_commit
theorem temporary_pc32_reference_memory_commit (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) (operation : MemoryOp)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (aligned : RetirementReferenceAligned (run initial inputs (t + 2))) :
    RetirementReferenceAligned (run initial inputs (t + 3)) := by
  rcases BitVec.eq_zero_or_eq_one (v11628 (run initial inputs (t + 1)) (inputs (t + 1))) with misaligned | addressAligned
  · have exception := reference_memory_exception_run initial inputs reset environment t operation commit unit matched registers
    have raised : v23407 (run initial inputs (t + 2)) (inputs (t + 2)) = 1 := by
      simpa [misaligned] using exception
    have trap := (committed_memory_trap_matches_reference_run initial inputs reset environment t operation
      commit unit matched registers).trans raised
    exact temporary_pc32_reference_trap_commit initial inputs reset environment restriction t currentReset commit trap raised
  · exact temporary_pc32_reference_aligned_memory_commit initial inputs reset environment restriction t operation
      currentReset commit unit matched registers addressAligned aligned

theorem temporary_pc32_reference_lsu_commit (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (aligned : RetirementReferenceAligned (run initial inputs (t + 2))) :
    RetirementReferenceAligned (run initial inputs (t + 3)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨operation, matched, _⟩ := original_assumptions_lsu_memory_run initial inputs reset environment t valid unit
  exact temporary_pc32_reference_memory_commit initial inputs reset environment restriction t operation
    currentReset commit unit matched registers aligned

#print axioms temporary_pc32_reference_memory_commit
#print axioms temporary_pc32_reference_lsu_commit
end NutShellProofs
