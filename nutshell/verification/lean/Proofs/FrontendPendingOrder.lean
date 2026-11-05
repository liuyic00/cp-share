import Proofs.IDUHandshake
namespace NutShellProofs
open nNutCore

theorem pending_fifo_transfer {α : Type} (queue : List α) (pending : Option α)
    (old fresh : α) (enqueue dequeue capture : Bool)
    (hasOld : enqueue = true → pending = some old)
    (replace : capture = true → pending ≠ none → enqueue = true)
    (nonempty : dequeue = true → queue ≠ []) :
    ((if dequeue then queue.tail else queue) ++ (if enqueue then [old] else [])) ++
      (if capture then some fresh else if enqueue then none else pending).toList =
    (if dequeue then (queue ++ pending.toList).tail else queue ++ pending.toList) ++
      (if capture then [fresh] else []) := by
  cases enqueue <;> cases dequeue <;> cases capture <;> cases pending <;>
    cases queue <;> simp_all [List.append_assoc]

def FrontendPending (s : State) : List (BitVec 64 × BitVec 39) :=
  QueueContents s ++ (IDUPending s).toList

theorem frontend_pending_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (flush : v30668 s i = 0)
    (bound : QueueOccupancy s ≤ 2) :
    FrontendPending (step s i) =
      (if v24283 s i = 1 then (FrontendPending s).tail else FrontendPending s) ++
      (if v11102 s i = 1 then [(v11105 s i, v10174 s i)] else []) := by
  have hasOld : v26198 s i = 1 → IDUPending s = some (IDUPair s) := by
    intro enqueue
    have valid := (queue_enqueue_single s i enqueue).1
    change s.g38.r1241_nfrontend_5Fvalid = 1 at valid
    simp [IDUPending, valid]
  have replace : v11102 s i = 1 → IDUPending s ≠ none → v26198 s i = 1 := by
    intro capture pending
    rcases BitVec.eq_zero_or_eq_one s.g38.r1241_nfrontend_5Fvalid with invalid | valid
    · simp [IDUPending, invalid] at pending
    · exact idu_capture_replaces_only_consumed s i valid capture
  have nonempty : v24283 s i = 1 → QueueContents s ≠ [] := by
    intro dequeue empty
    have front := queue_capture_is_front s i dequeue
    simp [empty] at front
  have transfer := pending_fifo_transfer (QueueContents s) (IDUPending s) (IDUPair s)
    (v11105 s i, v10174 s i) (decide (v26198 s i = 1))
    (decide (v24283 s i = 1)) (decide (v11102 s i = 1))
    (by simpa using hasOld) (by simpa using replace) (by simpa using nonempty)
  simpa only [FrontendPending, queue_contents_step s i reset flush bound,
    idu_pending_step s i reset flush, decide_eq_true_eq] using transfer

theorem frontend_pending_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    FrontendPending (step s i) = [] := by
  simp [FrontendPending, queue_contents_reset s i reset, idu_pending_reset s i reset]

theorem frontend_pending_flush (s : State) (i : Inputs) (flush : v30668 s i = 1) :
    FrontendPending (step s i) = [] := by
  simp [FrontendPending, queue_contents_flush s i flush, idu_pending_flush s i flush]

#print axioms frontend_pending_step

theorem frontend_capture_is_front (s : State) (i : Inputs) (capture : v24283 s i = 1) :
    (FrontendPending s).head? = some (v24297 s i, v24312 s i) := by
  have front := queue_capture_is_front s i capture
  unfold FrontendPending
  cases h : QueueContents s with
  | nil => simp [h] at front
  | cons pair rest => simpa [h] using front

/-- FIFO replay driven only by frontend capture and execution acceptance, not IDU enqueue. -/
def FrontendReplay (initial : State) (inputs : Nat → Inputs) : Nat → List (BitVec 64 × BitVec 39)
  | 0 => []
  | t + 1 =>
    let s := run initial inputs (t + 1)
    let i := inputs (t + 1)
    if i.g0.nreset = 1 ∨ v30668 s i = 1 then [] else
      (if v24283 s i = 1 then (FrontendReplay initial inputs t).tail else FrontendReplay initial inputs t) ++
        (if v11102 s i = 1 then [(v11105 s i, v10174 s i)] else [])

theorem frontend_pending_replay (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    FrontendPending (run initial inputs (t + 1)) = FrontendReplay initial inputs t := by
  induction t with
  | zero => exact frontend_pending_reset initial (inputs 0) reset
  | succ t ih =>
    rcases BitVec.eq_zero_or_eq_one (inputs (t + 1)).g0.nreset with noReset | activeReset
    · rcases BitVec.eq_zero_or_eq_one (v30668 (run initial inputs (t + 1)) (inputs (t + 1))) with noFlush | flush
      · have next := frontend_pending_step _ _ noReset noFlush (queue_occupancy_bound_run initial inputs reset t)
        rw [ih] at next
        simpa [FrontendReplay, noReset, noFlush] using next
      · have empty := frontend_pending_flush (run initial inputs (t + 1)) (inputs (t + 1)) flush
        simpa [FrontendReplay, noReset, flush] using empty
    · have empty := frontend_pending_reset (run initial inputs (t + 1)) (inputs (t + 1)) activeReset
      simpa [FrontendReplay, activeReset] using empty

theorem execute_capture_frontend_replay (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (capture : v24283 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    (FrontendReplay initial inputs t).head? = some
      ((run initial inputs (t + 2)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr,
        (run initial inputs (t + 2)).g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc) := by
  rw [← frontend_pending_replay initial inputs reset t]
  change _ = some (v24298 (run initial inputs (t + 1)) (inputs (t + 1)),
    v24313 (run initial inputs (t + 1)) (inputs (t + 1)))
  rw [v24298, v24313, if_pos capture, if_pos capture]
  exact frontend_capture_is_front _ _ capture

#print axioms frontend_pending_replay
#print axioms execute_capture_frontend_replay
end NutShellProofs
