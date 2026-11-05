import Proofs.ImmediateRegisterStep
import Proofs.ShiftRegisterStep
import Proofs.WordRegisterStep
import Proofs.AuipcCorrespondence
import Proofs.RegisterALURegisterStep
import Proofs.BranchRegisterStep
import Proofs.JumpRegisterRun
import Proofs.MemoryUnitPipeline
import Proofs.WhitelistFamilyCases
namespace NutShellProofs
open nNutCore

/-- ALU-dispatched whitelist cases preserve registers, retaining the PC induction
hypothesis required by AUIPC and jump link values. -/
theorem committed_alu_registers_preserved_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2))) :
    ArchitecturalRegistersAligned (run initial inputs (t + 3)) := by
  rcases BitVec.eq_zero_or_eq_one (inputs (t + 2)).g0.nreset with currentReset | currentReset
  · have valid := commit_requires_execute_valid _ _ _ commit
    have allowed := allowed_instruction_family _
      (original_assumptions_execute_allowed initial inputs reset environment t valid)
    rcases allowed with ⟨op, matched⟩ | ⟨op, matched⟩ | ⟨op, matched⟩ | ⟨op, matched⟩ |
      ⟨op, matched⟩ | ⟨op, matched⟩ | ⟨op, matched⟩ | ⟨op, matched⟩
    · exact immediate_registers_aligned_run_step initial inputs reset t op currentReset commit unit matched registers
    · exact shift_registers_aligned_run_step initial inputs reset t op currentReset commit unit matched registers
    · exact word_registers_aligned_run_step initial inputs reset t op currentReset commit unit matched registers
    · cases op with
      | lui => exact lui_registers_aligned_run_step initial inputs reset t currentReset commit unit matched registers
      | auipc => exact auipc_registers_aligned_run_step initial inputs reset t currentReset commit unit matched registers pc
    · exact register_alu_registers_aligned_run_step initial inputs reset t op currentReset commit unit matched registers
    · exact branch_registers_aligned_run_step initial inputs reset t op currentReset commit unit matched registers
    · exact jump_registers_aligned_run_step initial inputs reset t op currentReset (environment (t + 1)) commit unit matched registers pc
    · have memoryUnit := (memory_unit_decode_run initial inputs reset t).2 valid op matched
      change v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 ∨
        v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 3 at memoryUnit
      rw [unit] at memoryUnit
      simp at memoryUnit
  · exact registers_aligned_after_reset _ _ currentReset
#print axioms committed_alu_registers_preserved_run
end NutShellProofs
