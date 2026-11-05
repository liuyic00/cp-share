import Proofs.PipelineFrontier
import Proofs.RegisterReachability
import Proofs.EventCoverage
namespace RiscvMiniProofs
open nCoreSoc

theorem pipeline_pc_step (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pipeline : PipelinePc (run initial inputs t)) :
    PipelinePc (run initial inputs (t+1)) := by
  constructor
  · exact pipeline_writeback_pc_step initial inputs cycles reset env t ht agree pipeline
  · exact pipeline_ahead_step _ _ (reset.2.2 t ht) (env t)
      (fetch_excludes_legacy_return initial inputs cycles reset env t ht)
  · apply pipeline_frontier_step _ _ (reset.2.2 t ht) (env t)
      (fetch_excludes_legacy_return initial inputs cycles reset env t ht)
      (bubble_alignment_reachable initial inputs cycles reset env t ht)
      (started_zero_of_valid_reachable initial inputs cycles reset t ht) pipeline
    have reference := reference_pc_step_reachable initial inputs cycles reset env t ht agree pipeline.writeback
    simpa only [run, commit_iff_valid_writeback _ _ (reset.2.2 t ht)] using reference

-- Joint induction closes the earlier dependency between registers and PC.
-- The only trace premises are the original reset and environment predicates.
theorem registers_and_pipeline_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) :
    RegisterAgreement (run initial inputs t) ∧ PipelinePc (run initial inputs t) := by
  have base : RegisterAgreement (run initial inputs cycles) ∧ PipelinePc (run initial inputs cycles) := by
    constructor
    · exact registers_agree_at_reset_boundary initial inputs cycles reset
    · cases cycles with
      | zero => have := reset.1; omega
      | succ n => exact pipeline_pc_reset _ _ (reset.2.1 n (Nat.lt_succ_self n))
  induction t with
  | zero => have := reset.1; omega
  | succ t ih =>
    by_cases prev : cycles ≤ t
    · obtain ⟨agree, pipeline⟩ := ih prev
      constructor
      · rcases BitVec.eq_zero_or_eq_one (v964 (run initial inputs t) (inputs t)) with idle | commit
        · exact registers_agree_noncommit initial inputs cycles reset env t prev agree idle
        · have pc := pipeline.writeback ((commit_iff_valid_writeback _ _ (reset.2.2 t prev)).mp commit)
          exact (register_tasks_iff_next _ _ (reset.2.2 t prev) commit).mp
            (register_tasks_reachable_of_pc initial inputs cycles reset env t prev agree commit pc)
      · exact pipeline_pc_step initial inputs cycles reset env t prev agree pipeline
    · have eq : t + 1 = cycles := by omega
      simpa only [eq] using base

theorem pc_task_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) :
    TaskHolds ⟨7, by decide⟩ (run initial inputs t) (inputs t) :=
  (pc_task_iff_valid_agreement _ _ (reset.2.2 t ht)).mpr
    (registers_and_pipeline_reachable initial inputs cycles reset env t ht).2.writeback

theorem event_valid_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) :
    TaskHolds ⟨40, by decide⟩ (run initial inputs t) (inputs t) := by
  obtain ⟨agree, pipeline⟩ := registers_and_pipeline_reachable initial inputs cycles reset env t ht
  exact event_valid_reachable_of_pc initial inputs cycles reset env t ht agree pipeline.writeback

#print axioms registers_and_pipeline_reachable
#print axioms pc_task_reachable
#print axioms event_valid_reachable
end RiscvMiniProofs
