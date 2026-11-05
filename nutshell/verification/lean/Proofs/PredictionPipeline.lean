import Proofs.QueuePredictionData
import Proofs.FetchQueueFlags
namespace NutShellProofs
open nNutCore

def IDUPredictionSequential (s : State) : Prop :=
  s.g38.r1241_nfrontend_5Fvalid = 1 →
    s.g38.r1244_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpnpc =
      s.g38.r1243_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpc + 4

def QueuePredictionSequential (s : State) : Prop :=
  ∀ slot, QueueSlotOccupied s slot →
    (QueuePredictionPair s slot).1 = (QueuePredictionPair s slot).2 + 4

def EXUPredictionSequential (s : State) : Prop :=
  s.g47.r1511_nbackend_5Fvalid = 1 →
    s.g47.r1514_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpnpc =
      s.g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc + 4

theorem idu_prediction_step (s : State) (i : Inputs)
    (old : IDUPredictionSequential s)
    (source : i.g0.nreset = 0 → v14 s i = 0 → v11102 s i = 1 →
      v11139 s i = v10174 s i + 4) : IDUPredictionSequential (step s i) := by
  intro valid
  have normal : i.g0.nreset = 0 := by
    rcases BitVec.eq_zero_or_eq_one i.g0.nreset with h | h
    · exact h
    · change v11101 s i = 1 at valid
      simp [v11101, v0, h, v24] at valid
  have noFlush : v14 s i = 0 := by
    rcases BitVec.eq_zero_or_eq_one (v14 s i) with h | h
    · exact h
    · change v11101 s i = 1 at valid
      simp [v11101, v11100, v11095, v18, v17, h, v15, v24] at valid
  change v11140 s i = v11108 s i + 4
  by_cases fire : v11102 s i = 1
  · simpa [v11140, v11108, v11107, fire] using source normal noFlush fire
  · rw [v11140, v11108, if_neg fire, if_neg fire]
    apply old
    change v11101 s i = 1 at valid
    have notCapture : v11096 s i ≠ 1 := fire
    unfold v11101 at valid
    split at valid
    · simp [v24] at valid
    · unfold v11100 at valid
      split at valid
      · simp [v24] at valid
      · simp only [v11099, notCapture, ↓reduceIte] at valid
        unfold v11098 at valid
        split at valid
        · simp [v24] at valid
        · exact valid

theorem queue_prediction_empty (s : State)
    (empty : s.g59.r1899_nringBufferHead = s.g59.r1900_nringBufferTail) :
    QueuePredictionSequential s := by
  intro slot occupied
  simp [QueueSlotOccupied, RingSlotOccupied, empty] at occupied

theorem queue_prediction_step (s : State) (i : Inputs) (bound : QueueOccupancy s ≤ 2)
    (old : QueuePredictionSequential s) (idu : IDUPredictionSequential s) :
    QueuePredictionSequential (step s i) := by
  rcases BitVec.eq_zero_or_eq_one i.g0.nreset with normal | reset
  · rcases BitVec.eq_zero_or_eq_one (v30668 s i) with noFlush | flush
    · intro slot occupied
      have previous := queue_occupied_slot_step s i slot normal noFlush bound occupied
      rw [queue_prediction_pair_step s i slot normal]
      split
      · rename_i written
        exact idu (queue_enqueue_single s i written.1).1
      · rename_i notWritten
        exact old slot (previous.resolve_left notWritten)
    · obtain ⟨head, tail⟩ := queue_pointers_flush s i flush
      exact queue_prediction_empty _ (head.trans tail.symm)
  · obtain ⟨head, tail⟩ := queue_pointers_reset s i reset
    exact queue_prediction_empty _ (head.trans tail.symm)

theorem exu_prediction_step (s : State) (i : Inputs)
    (queue : QueuePredictionSequential s) (old : EXUPredictionSequential s) :
    EXUPredictionSequential (step s i) := by
  intro valid
  change v24328 s i = v24313 s i + 4
  by_cases fire : v24283 s i = 1
  · rw [v24328, v24313, if_pos fire, if_pos fire]
    have paired := queue _ (queue_tail_occupied_on_capture s i fire)
    rw [← queue_selected_prediction_pair s i] at paired
    exact paired
  · rw [v24328, v24313, if_neg fire, if_neg fire]
    exact old (execute_valid_backward s i i valid fire)

#print axioms idu_prediction_step
#print axioms queue_prediction_step
#print axioms exu_prediction_step

theorem temporary_pc32_prediction_pipeline_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) :
    IDUPredictionSequential (run initial inputs (t + 1)) ∧
    QueuePredictionSequential (run initial inputs (t + 1)) ∧
    EXUPredictionSequential (run initial inputs (t + 1)) := by
  induction t with
  | zero =>
    refine ⟨?_, ?_, ?_⟩
    · intro valid
      change v11101 initial (inputs 0) = 1 at valid
      simp [v11101, v0, reset, v24] at valid
    · obtain ⟨head, tail⟩ := queue_pointers_reset initial (inputs 0) reset
      exact queue_prediction_empty _ (head.trans tail.symm)
    · intro valid
      have clear := execute_valid_reset initial (inputs 0) (inputs 1) reset
      change (run initial inputs 1).g47.r1511_nbackend_5Fvalid = 0 at clear
      rw [clear] at valid
      contradiction
  | succ t ih =>
    exact ⟨idu_prediction_step _ _ ih.1
      (temporary_pc32_idu_capture_prediction initial inputs reset environment restriction t),
      queue_prediction_step _ _ (queue_occupancy_bound_run initial inputs reset t) ih.2.1 ih.1,
      exu_prediction_step _ _ ih.2.1 ih.2.2⟩

#print axioms temporary_pc32_prediction_pipeline_run
end NutShellProofs
