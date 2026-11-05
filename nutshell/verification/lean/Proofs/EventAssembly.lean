import Proofs.Assembly
import Proofs.EventPC

namespace NutShellProofs
open nNutCore

-- Tasks 46/47 are derived from PC/event validity on reset-initialized runs.
def IndependentTask (task : Fin 48) : Prop := RemainingTask task ∧ task.val ≠ 46 ∧ task.val ≠ 47

theorem assemble_independent_tasks (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (remaining : ∀ task, IndependentTask task →
      TaskHolds task (run initial inputs t) (inputs t)) :
    asserts (run initial inputs t) (inputs t) := by
  apply assemble_tasks
  intro task h
  by_cases last : task.val = 47
  · have eq : task = ⟨47, by decide⟩ := Fin.ext last
    subst task
    exact task_47_run_from_event_valid initial inputs reset t
      (remaining 43 (by unfold IndependentTask RemainingTask; decide))
  · by_cases pcEvent : task.val = 46
    · have eq : task = ⟨46, by decide⟩ := Fin.ext pcEvent
      subst task
      exact task_46_run_from_event_and_pc initial inputs reset t
        (remaining 43 (by unfold IndependentTask RemainingTask; decide))
        (remaining 10 (by unfold IndependentTask RemainingTask; decide))
    · exact remaining task ⟨h, pcEvent, last⟩

theorem correct_iff_independent (cycles : Nat) :
    CorrectAfterReset cycles ↔
      ∀ (initial : State) (inputs : Nat → Inputs),
        ResetPrefix inputs cycles → Environment initial inputs →
          ∀ t, cycles ≤ t → ∀ task, IndependentTask task →
            TaskHolds task (run initial inputs t) (inputs t) := by
  constructor
  · intro correct initial inputs reset env t _ task _
    exact (asserts_iff_tasks _ _).mp (correct initial inputs reset env t) task
  · intro remaining
    apply lift_after_reset
    intro initial inputs reset env t ht
    exact assemble_independent_tasks initial inputs (reset.2.1 0 reset.1) t
      (remaining initial inputs reset env t ht)

#print axioms correct_iff_independent
end NutShellProofs
