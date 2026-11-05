import Proofs.TemporaryRedirectAlignment
import Proofs.FrontendOutputPCAlignment
import Proofs.FetchAlignmentFromRedirect
namespace NutShellProofs
open nNutCore

structure FrontendPipelineAligned (s : State) (i : Inputs) : Prop where
  fetch : BitVec.extractLsb' 0 2 s.g33.r1065_nfrontend_5Fifu_5Fpc = 0
  response : FetchResponsePCAligned s
  queue : FetchQueuePCAligned s
  buffer : FrontendAlignedState s
  pipeline : OccupiedInstructionPCPipeline (fun _ pc => BitVec.extractLsb' 0 2 pc = 0) s
  redirect : v14 s i = 1 → BitVec.extractLsb' 0 2 (v2709 s i) = 0

theorem temporary_pc32_frontend_pipeline_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) :
    FrontendPipelineAligned (run initial inputs (t + 1)) (inputs (t + 1)) := by
  induction t with
  | zero =>
    refine ⟨?_, fetch_response_pc_reset _ _ reset, fetch_queue_pc_reset _ _ reset,
      frontend_aligned_state_reset _ _ reset, occupied_instruction_pc_reset _ _ _ reset, ?_⟩
    · change BitVec.extractLsb' 0 2 (v9675 initial (inputs 0)) = 0
      rw [v9675]
      have r : v1 initial (inputs 0) = 1 := reset
      rw [if_pos r]
      unfold v9671
      decide
    · intro redirect
      have idle := reset_has_no_next_commit initial (inputs 0) (inputs 1) reset
      change v9 (run initial inputs 1) (inputs 1) = 0 at idle
      simp [v14, v13, v12, v11, v10, idle] at redirect
  | succ t ih =>
    have head := fetch_queue_pc_selected _ (inputs (t + 1)) ih.queue
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · apply fetch_pc_alignment_step _ _ ih.fetch
      intro update
      by_cases redirect : v14 (run initial inputs (t + 1)) (inputs (t + 1)) = 1
      · simpa only [v2759, if_pos redirect] using ih.redirect redirect
      · have noPrediction : v2736 (run initial inputs (t + 1)) (inputs (t + 1)) ≠ 1 := by
          intro enabled
          exact redirect (prediction_update_requires_redirect (run initial inputs t)
            (inputs t) (inputs (t + 1)) (Or.inl enabled) update)
        have clear := crossline_latch_clear_run initial inputs reset t
        have sequential := fetch_sequential_target_aligned _ (inputs (t + 1)) ih.fetch
        simpa only [v2759, if_neg redirect, v2758, clear,
          show (0 : BitVec 1) ≠ 1 by decide, ↓reduceIte, v2757, if_neg noPrediction] using sequential
    · exact fetch_response_pc_step _ _ ih.response (fun _ => ih.fetch)
    · exact fetch_queue_pc_step _ _ ih.queue (fun enqueue => fetch_enqueue_pc_aligned _ _ ih.response enqueue)
    · exact frontend_aligned_state_step _ _ ih.buffer (environment (t + 1)) head
    · refine ⟨?_, ?_, ?_⟩
      · apply idu_instruction_pc_unflushed_step _ _ _ ih.pipeline.1
        intro noRedirect _
        exact frontend_output_pc_aligned _ _ ih.buffer head noRedirect
      · exact occupied_queue_relation_step _ _ _ (queue_occupancy_bound_run initial inputs reset t)
          ih.pipeline.2.1 ih.pipeline.1
      · exact occupied_exu_relation_step _ _ _ ih.pipeline.2.1 ih.pipeline.2.2
    · exact temporary_pc32_redirect_aligned_run initial inputs reset environment restriction t
        ih.pipeline.2.2

/-- Original frontend assertion with all alignment obligations discharged,
under only the previously documented PC32 restriction. -/
theorem temporary_pc32_frontend_task0_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) :
    TaskHolds 0 (run initial inputs t) (inputs t) := by
  apply frontend_task0_run_of_requests initial inputs reset environment _ t
  intro k _
  exact (temporary_pc32_frontend_pipeline_run initial inputs reset environment restriction k).fetch

#print axioms temporary_pc32_frontend_pipeline_run
#print axioms temporary_pc32_frontend_task0_run
end NutShellProofs
