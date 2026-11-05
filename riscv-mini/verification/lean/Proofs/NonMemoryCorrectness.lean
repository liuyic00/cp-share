import Proofs.PipelineReachability
import Proofs.RegisterTaskGating
import Proofs.Assembly
namespace RiscvMiniProofs
open nCoreSoc

theorem register_tasks_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) :
    RegisterTasks (run initial inputs t) (inputs t) := by
  rcases BitVec.eq_zero_or_eq_one (v964 (run initial inputs t) (inputs t)) with idle | commit
  · exact register_tasks_idle _ _ idle
  · obtain ⟨agree, pipeline⟩ := registers_and_pipeline_reachable initial inputs cycles reset env t ht
    exact register_tasks_reachable_of_pc initial inputs cycles reset env t ht agree commit
      (pipeline.writeback ((commit_iff_valid_writeback _ _ (reset.2.2 t ht)).mp commit))

-- Original tasks 7..44, with no added PC, register or event premise.
theorem nonmemory_tasks_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (task : Fin 45) (nonmemory : 7 ≤ task.val) :
    TaskHolds task (run initial inputs t) (inputs t) := by
  by_cases pc : task.val = 7
  · have eq : task = ⟨7, by decide⟩ := Fin.ext pc
    subst task
    exact pc_task_reachable initial inputs cycles reset env t ht
  by_cases zero : task.val = 8
  · have eq : task = ⟨8, by decide⟩ := Fin.ext zero
    subst task
    exact zero_register_task _ _
  have valid := event_valid_reachable initial inputs cycles reset env t ht
  by_cases event : task.val = 40
  · have eq : task = ⟨40, by decide⟩ := Fin.ext event
    subst task
    exact valid
  by_cases intr : task.val = 41
  · have eq : task = ⟨41, by decide⟩ := Fin.ext intr
    subst task
    exact event_interrupt_number_task _ _
  by_cases cause : task.val = 42
  · have eq : task = ⟨42, by decide⟩ := Fin.ext cause
    subst task
    exact (event_payloads_of_validity _ _ (env t) valid).1
  by_cases eventPc : task.val = 43
  · have eq : task = ⟨43, by decide⟩ := Fin.ext eventPc
    subst task
    exact (event_payloads_of_validity _ _ (env t) valid).2
  by_cases instruction : task.val = 44
  · have eq : task = ⟨44, by decide⟩ := Fin.ext instruction
    subst task
    exact event_instruction_of_validity _ _ valid
  exact register_tasks_at_index _ _
    (register_tasks_reachable initial inputs cycles reset env t ht) task (by omega) (by omega)

-- This is a reduction of the full target, not a proof of the seven memory tasks.
theorem correct_iff_memory (cycles : Nat) :
    CorrectAfterReset cycles ↔
      ∀ (initial : State) (inputs : Nat → Inputs),
        ResetPrefix inputs cycles → Environment initial inputs →
          ∀ t, cycles ≤ t → ∀ task : Fin 45, task.val < 7 →
            TaskHolds task (run initial inputs t) (inputs t) := by
  constructor
  · intro correct initial inputs reset env t _ task _
    exact (asserts_iff_tasks _ _).mp (correct initial inputs reset env t) task
  · intro memory
    apply lift_after_reset
    intro initial inputs reset env t ht
    apply (asserts_iff_tasks _ _).mpr
    intro task
    by_cases mem : task.val < 7
    · exact memory initial inputs reset env t ht task mem
    · exact nonmemory_tasks_reachable initial inputs cycles reset env t ht task (by omega)

#print axioms register_tasks_reachable
#print axioms nonmemory_tasks_reachable
#print axioms correct_iff_memory
end RiscvMiniProofs
