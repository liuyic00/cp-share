import Proofs.MemoryCauseEvent
import Proofs.MemoryInterruptEvent
import Proofs.EventPC
import Proofs.EventInstruction
namespace NutShellProofs
open nNutCore

/-- All five original event assertions on LSU commits, conditional on current
architectural register and PC correspondence. Alignment faults are included. -/
theorem committed_lsu_event_tasks_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2))) :
    TaskHolds 43 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 44 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 45 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 46 (run initial inputs (t + 2)) (inputs (t + 2)) ∧
    TaskHolds 47 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have event := committed_lsu_event_task43_run initial inputs reset environment t commit unit registers
  exact ⟨event,
    committed_lsu_event_task44_run initial inputs reset t commit unit,
    committed_lsu_event_task45_run initial inputs reset environment t commit unit registers,
    task_46_run_from_event_and_pc initial inputs reset (t + 2) event pc,
    task_47_run_from_event_valid initial inputs reset (t + 2) event⟩
#print axioms committed_lsu_event_tasks_run
end NutShellProofs
