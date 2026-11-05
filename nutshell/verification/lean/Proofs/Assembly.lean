import Proofs.Internal

namespace NutShellProofs
open nNutCore

-- Indexing the generated list is equivalent to its original conjunction.
theorem asserts_iff_tasks (s : State) (i : Inputs) :
    asserts s i ↔ ∀ task : Fin 48, TaskHolds task s i := by
  change (eval s i).assertions.all id = true ↔ _
  rw [List.all_eq_true]
  constructor
  · intro h task
    exact h _ (List.mem_of_getElem rfl)
  · intro h b hb
    obtain ⟨k, hk, he⟩ := List.getElem_of_mem hb
    have bound : k < 48 := by simpa only [assertion_count] using hk
    have ht := h ⟨k, bound⟩
    change (eval s i).assertions[k] = true at ht
    simpa only [he] using ht

-- This is an obligation list, not an additional environment assumption.
def RemainingTask (task : Fin 48) : Prop :=
  task.val ≠ 1 ∧ task.val ≠ 2 ∧ task.val ≠ 11

theorem assemble_tasks (s : State) (i : Inputs)
    (remaining : ∀ task, RemainingTask task → TaskHolds task s i) :
    asserts s i := by
  apply (asserts_iff_tasks s i).mpr
  intro task
  by_cases h1 : task.val = 1
  · have : task = ⟨1, by decide⟩ := Fin.ext h1
    subst task
    exact task_1_always s i
  by_cases h2 : task.val = 2
  · have : task = ⟨2, by decide⟩ := Fin.ext h2
    subst task
    exact task_2_always s i
  by_cases h11 : task.val = 11
  · have : task = ⟨11, by decide⟩ := Fin.ext h11
    subst task
    exact task_11_always s i
  exact remaining task ⟨h1, h2, h11⟩

-- Full reset-initialized correctness is EXACTLY equivalent to the remaining
-- post-reset obligations; this equivalence does not discharge those obligations.
theorem correct_iff_remaining (cycles : Nat) :
    CorrectAfterReset cycles ↔
      ∀ (initial : State) (inputs : Nat → Inputs),
        ResetPrefix inputs cycles → Environment initial inputs →
          ∀ t, cycles ≤ t → ∀ task, RemainingTask task →
            TaskHolds task (run initial inputs t) (inputs t) := by
  constructor
  · intro correct initial inputs reset env t _ task _
    exact (asserts_iff_tasks _ _).mp (correct initial inputs reset env t) task
  · intro remaining
    apply lift_after_reset
    intro initial inputs reset env t ht
    exact assemble_tasks _ _ (remaining initial inputs reset env t ht)

#print axioms correct_iff_remaining
end NutShellProofs
