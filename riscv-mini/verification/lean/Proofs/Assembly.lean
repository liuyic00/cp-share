import Proofs.Events
import Proofs.ZeroRegister

namespace RiscvMiniProofs
open nCoreSoc

-- Indexing the generated list is equivalent to its original conjunction.
theorem asserts_iff_tasks (s : State) (i : Inputs) :
    asserts s i ↔ ∀ task : Fin 45, TaskHolds task s i := by
  change (eval s i).assertions.all id = true ↔ _
  rw [List.all_eq_true]
  constructor
  · intro h task
    exact h _ (List.mem_of_getElem rfl)
  · intro h b hb
    obtain ⟨k, hk, he⟩ := List.getElem_of_mem hb
    have bound : k < 45 := by simpa only [assertion_count] using hk
    have ht := h ⟨k, bound⟩
    change (eval s i).assertions[k] = true at ht
    simpa only [he] using ht

-- The two discharged tasks and three proved dependencies leave 40 independent
-- obligations. This predicate does NOT become an environment assumption.
def RemainingTask (task : Fin 45) : Prop :=
  task.val ≠ 8 ∧ task.val ≠ 41 ∧ task.val ≠ 42 ∧ task.val ≠ 43 ∧ task.val ≠ 44

theorem assemble_tasks (s : State) (i : Inputs) (env : assumes s i)
    (remaining : ∀ task, RemainingTask task → TaskHolds task s i) :
    asserts s i := by
  apply (asserts_iff_tasks s i).mpr
  intro task
  by_cases h8 : task.val = 8
  · have : task = ⟨8, by decide⟩ := Fin.ext h8
    subst task
    exact zero_register_task s i
  by_cases h41 : task.val = 41
  · have : task = ⟨41, by decide⟩ := Fin.ext h41
    subst task
    exact event_interrupt_number_task s i
  have valid : TaskHolds ⟨40, by decide⟩ s i :=
    remaining ⟨40, by decide⟩ (by simp [RemainingTask])
  by_cases h42 : task.val = 42
  · have : task = ⟨42, by decide⟩ := Fin.ext h42
    subst task
    exact (event_payloads_of_validity s i env valid).1
  by_cases h43 : task.val = 43
  · have : task = ⟨43, by decide⟩ := Fin.ext h43
    subst task
    exact (event_payloads_of_validity s i env valid).2
  by_cases h44 : task.val = 44
  · have : task = ⟨44, by decide⟩ := Fin.ext h44
    subst task
    apply event_instruction_of_validity
    exact remaining ⟨40, by decide⟩ (by simp [RemainingTask])
  exact remaining task ⟨h8, h41, h42, h43, h44⟩

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
    exact assemble_tasks _ _ (env t) (remaining initial inputs reset env t ht)

#print axioms correct_iff_remaining
end RiscvMiniProofs
