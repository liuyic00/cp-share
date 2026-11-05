import Proofs.TemporaryRegisterStep
import Proofs.MemoryCommitPC
import Proofs.UncorrectedJumpPC
import Proofs.BranchCommitPC
namespace NutShellProofs
open nNutCore

theorem temporary_pc32_pc_preserved_step (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (aligned : RetirementReferenceAligned (run initial inputs (t + 2))) :
    RetirementReferenceAligned (run initial inputs (t + 3)) := by
  rcases BitVec.eq_zero_or_eq_one (inputs (t + 2)).g0.nreset with currentReset | currentReset
  · rcases BitVec.eq_zero_or_eq_one (v9 (run initial inputs (t + 2)) (inputs (t + 2))) with idle | commit
    · exact temporary_pc32_retirement_reference_idle initial inputs reset environment restriction (t + 1)
        currentReset idle aligned
    · have valid := commit_requires_execute_valid _ _ _ commit
      rcases temporary_pc32_execute_alulsu initial inputs reset environment restriction t valid with unit | unit
      · have allowed := allowed_instruction_family _
          (original_assumptions_execute_allowed initial inputs reset environment t valid)
        rcases allowed with ⟨op, matched⟩ | ⟨op, matched⟩ | ⟨op, matched⟩ | ⟨op, matched⟩ |
          ⟨op, matched⟩ | ⟨op, matched⟩ | ⟨op, matched⟩ | ⟨op, matched⟩
        · exact temporary_pc32_reference_immediate_commit initial inputs reset environment restriction t op
            currentReset commit unit matched aligned
        · exact temporary_pc32_reference_shift_commit initial inputs reset environment restriction t op
            currentReset commit unit matched aligned
        · exact temporary_pc32_reference_word_commit initial inputs reset environment restriction t op
            currentReset commit unit matched aligned
        · exact temporary_pc32_reference_upper_commit initial inputs reset environment restriction t op
            currentReset commit unit matched aligned
        · exact temporary_pc32_reference_register_alu_commit initial inputs reset environment restriction t op
            currentReset commit unit matched aligned
        · exact temporary_pc32_reference_branch_commit initial inputs reset environment restriction t op
            currentReset commit unit matched registers aligned
        · cases op with
          | jal =>
            exact temporary_pc32_reference_jal_commit initial inputs reset environment restriction t
              currentReset commit unit matched aligned
          | jalr =>
            exact temporary_pc32_reference_jalr_commit initial inputs reset environment restriction t
              currentReset commit unit matched registers
        · have memoryUnit := (memory_unit_decode_run initial inputs reset t).2 valid op matched
          change v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 ∨
            v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 3 at memoryUnit
          rw [unit] at memoryUnit
          simp at memoryUnit
      · exact temporary_pc32_reference_lsu_commit initial inputs reset environment restriction t
          currentReset commit unit registers aligned
  · exact retirement_reference_reset _ _ currentReset

#print axioms temporary_pc32_pc_preserved_step
end NutShellProofs
