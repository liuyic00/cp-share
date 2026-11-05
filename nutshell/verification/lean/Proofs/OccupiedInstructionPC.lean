import Proofs.QueueSlotData
namespace NutShellProofs
open nNutCore

def OccupiedQueueRelation (relation : BitVec 64 → BitVec 39 → Prop) (s : State) : Prop :=
  ∀ slot, QueueSlotOccupied s slot → relation (QueuePair s slot).1 (QueuePair s slot).2

theorem occupied_queue_empty (relation : BitVec 64 → BitVec 39 → Prop) (s : State)
    (empty : s.g59.r1899_nringBufferHead = s.g59.r1900_nringBufferTail) :
    OccupiedQueueRelation relation s := by
  intro slot occupied
  simp [QueueSlotOccupied, RingSlotOccupied, empty] at occupied

theorem occupied_queue_relation_step (relation : BitVec 64 → BitVec 39 → Prop)
    (s : State) (i : Inputs) (bound : QueueOccupancy s ≤ 2)
    (old : OccupiedQueueRelation relation s) (idu : IDUInstructionPC relation s) :
    OccupiedQueueRelation relation (step s i) := by
  rcases BitVec.eq_zero_or_eq_one i.g0.nreset with noReset | reset
  · rcases BitVec.eq_zero_or_eq_one (v30668 s i) with noFlush | flush
    · intro slot occupied
      have previous := queue_occupied_slot_step s i slot noReset noFlush bound occupied
      rw [queue_pair_step s i slot noReset]
      split
      · rename_i written
        exact idu (queue_enqueue_single s i written.1).1
      · rename_i notWritten
        exact old slot (previous.resolve_left notWritten)
    · rcases queue_pointers_flush s i flush with ⟨head, tail⟩
      exact occupied_queue_empty relation _ (head.trans tail.symm)
  · rcases queue_pointers_reset s i reset with ⟨head, tail⟩
    exact occupied_queue_empty relation _ (head.trans tail.symm)

theorem occupied_exu_relation_step (relation : BitVec 64 → BitVec 39 → Prop)
    (s : State) (i : Inputs) (queue : OccupiedQueueRelation relation s)
    (old : EXUInstructionPC relation s) : EXUInstructionPC relation (step s i) := by
  intro valid
  change relation (v24298 s i) (v24313 s i)
  by_cases fire : v24283 s i = 1
  · rw [v24298, v24313, if_pos fire, if_pos fire]
    have paired := queue _ (queue_tail_occupied_on_capture s i fire)
    rw [← queue_selected_pair s i] at paired
    exact paired
  · rw [v24298, v24313, if_neg fire, if_neg fire]
    exact old (execute_valid_backward s i i valid fire)

def OccupiedInstructionPCPipeline (relation : BitVec 64 → BitVec 39 → Prop) (s : State) : Prop :=
  IDUInstructionPC relation s ∧ OccupiedQueueRelation relation s ∧ EXUInstructionPC relation s

theorem occupied_instruction_pc_reset (relation : BitVec 64 → BitVec 39 → Prop)
    (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    OccupiedInstructionPCPipeline relation (step s i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro valid
    change v11101 s i = 1 at valid
    simp [v11101, v0, v24, reset] at valid
  · rcases queue_pointers_reset s i reset with ⟨head, tail⟩
    exact occupied_queue_empty relation _ (head.trans tail.symm)
  · intro valid
    have clear := execute_valid_reset s i i reset
    change (step s i).g47.r1511_nbackend_5Fvalid = 0 at clear
    rw [clear] at valid
    contradiction

theorem occupied_instruction_pc_prefix (relation : BitVec 64 → BitVec 39 → Prop)
    (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (source : ∀ k, k ≤ t → v11102 (run initial inputs k) (inputs k) = 1 →
      relation (v11105 (run initial inputs k) (inputs k))
        (v10174 (run initial inputs k) (inputs k))) :
    OccupiedInstructionPCPipeline relation (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact occupied_instruction_pc_reset relation initial (inputs 0) reset
  | succ t ih =>
    rcases ih (fun k hk => source k (by omega)) with ⟨idu, queue, exu⟩
    exact ⟨idu_instruction_pc_relation_step relation _ _ idu (source (t + 1) (by omega)),
      occupied_queue_relation_step relation _ _ (queue_occupancy_bound_run initial inputs reset t) queue idu,
      occupied_exu_relation_step relation _ _ queue exu⟩

/-- An occupied valid execute pair has a real earlier frontend capture; no reset alternative. -/
theorem execute_instruction_pc_captured (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (valid : (run initial inputs (t + 1)).g47.r1511_nbackend_5Fvalid = 1) :
    ∃ k, k ≤ t ∧ v11102 (run initial inputs k) (inputs k) = 1 ∧
      (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr =
        v11105 (run initial inputs k) (inputs k) ∧
      (run initial inputs (t + 1)).g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc =
        v10174 (run initial inputs k) (inputs k) := by
  let relation := fun instr pc => ∃ k, k ≤ t ∧
    v11102 (run initial inputs k) (inputs k) = 1 ∧
    instr = v11105 (run initial inputs k) (inputs k) ∧
    pc = v10174 (run initial inputs k) (inputs k)
  have pipeline := occupied_instruction_pc_prefix relation initial inputs reset t
    (fun k bound capture => ⟨k, bound, capture, rfl, rfl⟩)
  exact pipeline.2.2 valid

#print axioms occupied_instruction_pc_prefix
#print axioms execute_instruction_pc_captured
end NutShellProofs
