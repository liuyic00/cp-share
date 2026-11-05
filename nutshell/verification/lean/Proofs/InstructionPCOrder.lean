import Proofs.FetchToIDUOrder
import Proofs.PipelinePendingOrder
namespace NutShellProofs
open nNutCore

/-- PCs in execution order, spanning the backend and fetch FIFO. -/
def InstructionPCs (s : State) : List (BitVec 39) :=
  (PipelinePending s).map Prod.snd ++ FetchPCContents s

theorem fifo_internal_transfer {α : Type} (back front : List α) (accepted : α)
    (transfer complete : Bool)
    (first : transfer = true → front.head? = some accepted)
    (valid : complete = true → back ≠ []) :
    ((if complete then back.tail else back) ++ (if transfer then [accepted] else [])) ++
      (if transfer then front.tail else front) =
    if complete then (back ++ front).tail else back ++ front := by
  cases transfer <;> cases complete <;> cases back <;> cases front <;>
    simp_all [List.append_assoc]

theorem instruction_pcs_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (flush : v14 s i = 0)
    (bound : QueueOccupancy s ≤ 2)
    (handshake : v11083 s i = v11102 s i)
    (front : v11102 s i = 1 → (FetchPCContents s).head? = some (v10174 s i)) :
    InstructionPCs (step s i) =
      (if v11702 s i = 1 then (InstructionPCs s).tail else InstructionPCs s) ++
      (if v10241 s i = 1 then [v10265 s i] else []) := by
  have valid : v11702 s i = 1 → (PipelinePending s).map Prod.snd ≠ [] := by
    intro complete
    simp [PipelinePending, EXUPending, execute_completion_requires_valid s i complete]
  have transfer := fifo_internal_transfer ((PipelinePending s).map Prod.snd)
    (FetchPCContents s) (v10174 s i) (decide (v11102 s i = 1))
    (decide (v11702 s i = 1)) (by simpa using front) (by simpa using valid)
  simp only [decide_eq_true_eq] at transfer
  unfold InstructionPCs
  rw [pipeline_pending_step s i reset flush bound, fetch_pc_contents_step s i reset flush,
    handshake]
  simp only [List.map_append]
  have mapped :
      (if v11702 s i = 1 then (PipelinePending s).tail else PipelinePending s).map Prod.snd =
      if v11702 s i = 1 then ((PipelinePending s).map Prod.snd).tail
      else (PipelinePending s).map Prod.snd := by
    split <;> simp_all
  rw [mapped]
  have incoming : (if v11102 s i = 1 then [(v11105 s i, v10174 s i)] else []).map Prod.snd =
      if v11102 s i = 1 then [v10174 s i] else [] := by
    split <;> simp_all
  rw [incoming, ← List.append_assoc, transfer]

theorem instruction_pcs_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    InstructionPCs (step s i) = [] := by
  simp [InstructionPCs, pipeline_pending_reset s i reset, fetch_pc_contents_reset s i reset]

theorem instruction_pcs_flush (s : State) (i : Inputs) (flush : v14 s i = 1) :
    InstructionPCs (step s i) = [] := by
  simp [InstructionPCs, pipeline_pending_flush s i flush, fetch_pc_contents_flush s i flush]

#print axioms instruction_pcs_step

theorem temporary_pc32_instruction_pcs_step (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (currentReset : (inputs (t + 1)).g0.nreset = 0)
    (noRedirect : v14 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    InstructionPCs (run initial inputs (t + 2)) =
      (if v11702 (run initial inputs (t + 1)) (inputs (t + 1)) = 1
       then (InstructionPCs (run initial inputs (t + 1))).tail
       else InstructionPCs (run initial inputs (t + 1))) ++
      (if v10241 (run initial inputs (t + 1)) (inputs (t + 1)) = 1
       then [v10265 (run initial inputs (t + 1)) (inputs (t + 1))] else []) := by
  exact instruction_pcs_step _ _ currentReset noRedirect
    (queue_occupancy_bound_run initial inputs reset t)
    (temporary_pc32_dequeue_eq_capture_run initial inputs reset environment restriction t
      currentReset noRedirect)
    (temporary_pc32_idu_capture_front initial inputs reset environment restriction t
      currentReset noRedirect)

theorem execute_completion_is_instruction_pc_front (s : State) (i : Inputs)
    (complete : v11702 s i = 1) :
    (InstructionPCs s).head? = some (EXUPair s).2 := by
  simp [InstructionPCs, PipelinePending, EXUPending,
    execute_completion_requires_valid s i complete]

theorem committed_pc_is_instruction_front (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) :
    (InstructionPCs s).head? = some (WBUPair (step s i)).2 := by
  have captured := commit_requires_capture s i next commit
  have complete : v11702 s i = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v11702 s i) with idle | done
    · simp [v25332, idle] at captured
    · exact done
  rw [committed_pair_is_execute_pair s i next commit]
  exact execute_completion_is_instruction_pc_front s i complete

#print axioms temporary_pc32_instruction_pcs_step
#print axioms committed_pc_is_instruction_front
end NutShellProofs
