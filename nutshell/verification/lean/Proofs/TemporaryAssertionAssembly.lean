import Proofs.TemporaryRegisterTasks
import Proofs.TemporaryEventInvariant
import Proofs.TemporaryMemoryTasks
import Proofs.TemporaryFrontendInvariant
namespace NutShellProofs
open nNutCore

/-- Original memory assertions at every cycle, conditional on the PC invariant. -/
theorem temporary_pc32_memory_tasks_of_pc (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs)
    (pc : ∀ k, TaskHolds 10 (run initial inputs (k + 2)) (inputs (k + 2)))
    (t : Nat) (task : Fin 48) (lo : 3 ≤ task.val) (hi : task.val ≤ 9) :
    TaskHolds task (run initial inputs t) (inputs t) := by
  cases t with
  | zero => exact (asserts_iff_tasks _ _).mp (assertions_during_reset _ _ reset) task
  | succ t =>
    cases t with
    | zero => exact no_commit_memory_tasks _ _ (reset_has_no_next_commit _ _ _ reset) task lo hi
    | succ t =>
      exact temporary_pc32_memory_tasks_run initial inputs reset environment restriction t
        (temporary_pc32_registers_run_of_pc initial inputs reset environment restriction pc (t + 1)) task lo hi

/-- This proves a reduction of the original conjunction, not its remaining PC
and frontend obligations. Neither obligation is added to Environment. -/
theorem temporary_pc32_asserts_of_frontend_and_pc (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs)
    (frontend : ∀ t, TaskHolds 0 (run initial inputs t) (inputs t))
    (pc : ∀ t, TaskHolds 10 (run initial inputs t) (inputs t))
    (t : Nat) : asserts (run initial inputs t) (inputs t) := by
  apply assemble_tasks
  intro task remaining
  by_cases front : task.val = 0
  · have eq : task = 0 := Fin.ext front
    subst task
    exact frontend t
  by_cases programCounter : task.val = 10
  · have eq : task = 10 := Fin.ext programCounter
    subst task
    exact pc t
  by_cases memory : task.val ≤ 9
  · exact temporary_pc32_memory_tasks_of_pc initial inputs reset environment restriction
      (fun k => pc (k + 2)) t task (by rcases remaining with ⟨a,b,c⟩; omega) memory
  by_cases registers : task.val ≤ 42
  · exact temporary_pc32_register_tasks_run_of_pc initial inputs reset environment restriction
      (fun k => pc (k + 2)) t task (by rcases remaining with ⟨a,b,c⟩; omega) registers
  have events := temporary_pc32_events_run_of_pc initial inputs reset environment restriction (fun k => pc (k + 2)) t
  have cases : task = 43 ∨ task = 44 ∨ task = 45 ∨ task = 46 ∨ task = 47 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl
  · exact events.1
  · exact events.2.1
  · exact events.2.2.1
  · exact events.2.2.2.1
  · exact events.2.2.2.2
/-- Frontend task zero is now discharged by the joint pipeline invariant.
Only architectural PC correspondence remains an explicit proof obligation. -/
theorem temporary_pc32_asserts_of_pc (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs)
    (pc : ∀ t, TaskHolds 10 (run initial inputs t) (inputs t))
    (t : Nat) : asserts (run initial inputs t) (inputs t) := by
  exact temporary_pc32_asserts_of_frontend_and_pc initial inputs reset environment restriction
    (temporary_pc32_frontend_task0_run initial inputs reset environment restriction) pc t

#print axioms temporary_pc32_asserts_of_pc
#print axioms temporary_pc32_memory_tasks_of_pc
#print axioms temporary_pc32_asserts_of_frontend_and_pc
end NutShellProofs
