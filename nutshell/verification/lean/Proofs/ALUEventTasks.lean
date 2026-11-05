import Proofs.ImmediateEventRun
import Proofs.ShiftEventRun
import Proofs.WordEventRun
import Proofs.UpperEventRun
import Proofs.RegisterALUEventRun
import Proofs.BranchEventRun
import Proofs.JumpEventRun
import Proofs.MemoryUnitPipeline
import Proofs.WhitelistFamilyCases
namespace NutShellProofs
open nNutCore

/-- All original event assertions for ALU-dispatched whitelist instructions.
Register and PC correspondence remain explicit for branches and jumps. -/
theorem committed_alu_event_tasks_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2))) :
    TaskHolds 43 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 44 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 45 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 46 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 47 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have allowed := allowed_instruction_family _
    (original_assumptions_execute_allowed initial inputs reset environment t valid)
  rcases allowed with ⟨op, matched⟩ | ⟨op, matched⟩ | ⟨op, matched⟩ | ⟨op, matched⟩ |
    ⟨op, matched⟩ | ⟨op, matched⟩ | ⟨op, matched⟩ | ⟨op, matched⟩
  · exact immediate_event_tasks_run initial inputs reset t op environment commit unit matched
  · exact shift_event_tasks_run initial inputs reset t op environment commit unit matched
  · exact word_event_tasks_run initial inputs reset t op environment commit unit matched
  · exact upper_event_tasks_run initial inputs reset t op environment commit unit matched
  · exact register_alu_event_tasks_run initial inputs reset t op environment commit unit matched
  · exact branch_event_tasks_run initial inputs reset t op currentReset environment commit unit matched registers pc
  · cases op with
    | jal => exact jal_event_tasks_run initial inputs reset t currentReset environment commit unit matched pc
    | jalr => exact jalr_event_tasks_run initial inputs reset t environment commit unit matched registers
  · have memoryUnit := (memory_unit_decode_run initial inputs reset t).2 valid op matched
    change v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 ∨
      v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 3 at memoryUnit
    rw [unit] at memoryUnit
    simp at memoryUnit

#print axioms committed_alu_event_tasks_run
end NutShellProofs
