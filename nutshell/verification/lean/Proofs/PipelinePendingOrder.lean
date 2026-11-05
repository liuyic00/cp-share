import Proofs.ExecuteHandshake
namespace NutShellProofs
open nNutCore

theorem pipeline_flush_signals (s : State) (i : Inputs) :
    v30668 s i = v14 s i ∧ v24276 s i = v14 s i ∧ v25328 s i = v14 s i := by
  rcases BitVec.eq_zero_or_eq_one (v14 s i) with clear | active
  all_goals simp_all [v30668, v24276, v25328, v21, v20, v19, v18, v17, v15, v16]

theorem execute_fifo_transfer {α : Type} (front : List α) (pending : Option α)
    (accepted : α) (transfer complete : Bool)
    (first : transfer = true → front.head? = some accepted)
    (valid : complete = true → pending ≠ none)
    (replace : transfer = true → pending ≠ none → complete = true) :
    (if transfer then some accepted else if complete then none else pending).toList ++
      (if transfer then front.tail else front) =
    if complete then (pending.toList ++ front).tail else pending.toList ++ front := by
  cases transfer <;> cases complete <;> cases pending <;> cases front <;>
    simp_all [List.append_assoc]

def PipelinePending (s : State) : List (BitVec 64 × BitVec 39) :=
  (EXUPending s).toList ++ FrontendPending s

theorem pipeline_pending_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (flush : v14 s i = 0)
    (bound : QueueOccupancy s ≤ 2) :
    PipelinePending (step s i) =
      (if v11702 s i = 1 then (PipelinePending s).tail else PipelinePending s) ++
      (if v11102 s i = 1 then [(v11105 s i, v10174 s i)] else []) := by
  have signals := pipeline_flush_signals s i
  have frontFlush : v30668 s i = 0 := signals.1.trans flush
  have exuFlush : v24276 s i = 0 := signals.2.1.trans flush
  have valid : v11702 s i = 1 → EXUPending s ≠ none := by
    intro complete
    simp [EXUPending, execute_completion_requires_valid s i complete]
  have replace : v24283 s i = 1 → EXUPending s ≠ none → v11702 s i = 1 := by
    intro capture pending
    rcases BitVec.eq_zero_or_eq_one s.g47.r1511_nbackend_5Fvalid with idle | active
    · simp [EXUPending, idle] at pending
    · exact execute_capture_replaces_only_completed s i active capture
  have transfer := execute_fifo_transfer (FrontendPending s) (EXUPending s)
    (v24297 s i, v24312 s i) (decide (v24283 s i = 1)) (decide (v11702 s i = 1))
    (by simpa using frontend_capture_is_front s i) (by simpa using valid) (by simpa using replace)
  simp only [decide_eq_true_eq] at transfer
  unfold PipelinePending
  rw [execute_pending_step s i reset exuFlush, frontend_pending_step s i reset frontFlush bound]
  rw [← List.append_assoc, transfer]

theorem pipeline_pending_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    PipelinePending (step s i) = [] := by
  simp [PipelinePending, execute_pending_reset s i reset, frontend_pending_reset s i reset]

theorem pipeline_pending_flush (s : State) (i : Inputs) (flush : v14 s i = 1) :
    PipelinePending (step s i) = [] := by
  have signals := pipeline_flush_signals s i
  simp [PipelinePending, execute_pending_flush s i (signals.2.1.trans flush),
    frontend_pending_flush s i (signals.1.trans flush)]

theorem execute_completion_is_pipeline_front (s : State) (i : Inputs)
    (complete : v11702 s i = 1) : (PipelinePending s).head? = some (EXUPair s) := by
  simp [PipelinePending, EXUPending, execute_completion_requires_valid s i complete]

#print axioms pipeline_pending_step
#print axioms execute_completion_is_pipeline_front

def PipelineReplay (initial : State) (inputs : Nat → Inputs) : Nat → List (BitVec 64 × BitVec 39)
  | 0 => []
  | t + 1 =>
    let s := run initial inputs (t + 1)
    let i := inputs (t + 1)
    if i.g0.nreset = 1 ∨ v14 s i = 1 then [] else
      (if v11702 s i = 1 then (PipelineReplay initial inputs t).tail else PipelineReplay initial inputs t) ++
        (if v11102 s i = 1 then [(v11105 s i, v10174 s i)] else [])

theorem pipeline_pending_replay (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    PipelinePending (run initial inputs (t + 1)) = PipelineReplay initial inputs t := by
  induction t with
  | zero => exact pipeline_pending_reset initial (inputs 0) reset
  | succ t ih =>
    rcases BitVec.eq_zero_or_eq_one (inputs (t + 1)).g0.nreset with noReset | activeReset
    · rcases BitVec.eq_zero_or_eq_one (v14 (run initial inputs (t + 1)) (inputs (t + 1))) with noFlush | flush
      · have next := pipeline_pending_step _ _ noReset noFlush (queue_occupancy_bound_run initial inputs reset t)
        rw [ih] at next
        simpa [PipelineReplay, noReset, noFlush] using next
      · have empty := pipeline_pending_flush (run initial inputs (t + 1)) (inputs (t + 1)) flush
        simpa [PipelineReplay, noReset, flush] using empty
    · have empty := pipeline_pending_reset (run initial inputs (t + 1)) (inputs (t + 1)) activeReset
      simpa [PipelineReplay, activeReset] using empty


theorem execute_completion_replay_front (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (complete : v11702 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    (PipelineReplay initial inputs t).head? = some (EXUPair (run initial inputs (t + 1))) := by
  rw [← pipeline_pending_replay initial inputs reset t]
  exact execute_completion_is_pipeline_front _ _ complete

#print axioms pipeline_pending_replay
#print axioms execute_completion_replay_front

def WBUPair (s : State) : BitVec 64 × BitVec 39 :=
  (s.g49.r1568_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fcf_5Finstr,
    s.g49.r1569_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fcf_5Fpc)

theorem committed_pair_is_execute_pair (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) : WBUPair (step s i) = EXUPair s := by
  have instr := capture_decode_cf_instr s i next commit
  have pc := capture_decode_cf_pc s i next commit
  unfold WBUPair
  rw [instr, pc]
  rfl

theorem committed_pair_replay_front (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1) :
    (PipelineReplay initial inputs t).head? = some (WBUPair (run initial inputs (t + 2))) := by
  have captured := commit_requires_capture _ _ _ commit
  have complete : v11702 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v11702 (run initial inputs (t + 1)) (inputs (t + 1))) with idle | done
    · simp [v25332, idle] at captured
    · exact done
  change _ = some (WBUPair (step (run initial inputs (t + 1)) (inputs (t + 1))))
  rw [committed_pair_is_execute_pair _ _ _ commit]
  exact execute_completion_replay_front initial inputs reset t complete

#print axioms committed_pair_replay_front
end NutShellProofs
