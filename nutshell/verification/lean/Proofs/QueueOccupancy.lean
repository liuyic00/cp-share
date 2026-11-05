import Proofs.QueuePointers
namespace NutShellProofs
open nNutCore

def QueueOccupancy (s : State) : Nat :=
  (s.g59.r1899_nringBufferHead - s.g59.r1900_nringBufferTail).toNat

/-- Finite modulo-four arithmetic, checked by kernel reduction. -/
theorem queue_pointer_arithmetic : ∀ (head tail : BitVec 2) (enq deq : Bool),
    (head - tail).toNat ≤ 2 →
    (enq = true → head + 1 ≠ tail ∧ head + 2 ≠ tail) →
    (deq = true → head ≠ tail) →
    ((if enq then head + 1 else head) -
      (if deq then tail + 1 else tail)).toNat + (if deq then 1 else 0) =
      (head - tail).toNat + (if enq then 1 else 0) ∧
    ((if enq then head + 1 else head) -
      (if deq then tail + 1 else tail)).toNat ≤ 2 := by decide

theorem queue_occupancy_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (flush : v30668 s i = 0)
    (bound : QueueOccupancy s ≤ 2) :
    QueueOccupancy (step s i) + (if v24283 s i = 1 then 1 else 0) =
      QueueOccupancy s + (if v26198 s i = 1 then 1 else 0) ∧
    QueueOccupancy (step s i) ≤ 2 := by
  have room := queue_enqueue_has_room s i
  have nonempty := execute_capture_queue_nonempty s i
  have arithmetic := queue_pointer_arithmetic s.g59.r1899_nringBufferHead
    s.g59.r1900_nringBufferTail (decide (v26198 s i = 1)) (decide (v24283 s i = 1))
    bound (by simpa using room) (by simpa using nonempty)
  simpa only [QueueOccupancy, queue_head_step s i reset flush,
    queue_tail_step s i reset flush, decide_eq_true_eq] using arithmetic

theorem queue_occupancy_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueOccupancy (step s i) = 0 := by
  rcases queue_pointers_reset s i reset with ⟨head, tail⟩
  simp [QueueOccupancy, head, tail]

theorem queue_occupancy_flush (s : State) (i : Inputs) (flush : v30668 s i = 1) :
    QueueOccupancy (step s i) = 0 := by
  rcases queue_pointers_flush s i flush with ⟨head, tail⟩
  simp [QueueOccupancy, head, tail]

theorem queue_occupancy_bound_step (s : State) (i : Inputs)
    (bound : QueueOccupancy s ≤ 2) : QueueOccupancy (step s i) ≤ 2 := by
  rcases BitVec.eq_zero_or_eq_one i.g0.nreset with noReset | reset
  · rcases BitVec.eq_zero_or_eq_one (v30668 s i) with noFlush | flush
    · exact (queue_occupancy_step s i noReset noFlush bound).2
    · rw [queue_occupancy_flush s i flush]; decide
  · rw [queue_occupancy_reset s i reset]; decide

theorem queue_occupancy_bound_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    QueueOccupancy (run initial inputs (t + 1)) ≤ 2 := by
  induction t with
  | zero =>
    change QueueOccupancy (step initial (inputs 0)) ≤ 2
    rw [queue_occupancy_reset initial (inputs 0) reset]
    decide
  | succ t ih => exact queue_occupancy_bound_step _ _ ih

#print axioms queue_pointer_arithmetic
#print axioms queue_occupancy_bound_run
#print axioms queue_occupancy_step

/-- The half-open circular interval from tail to head. -/
def RingSlotOccupied (head tail slot : BitVec 2) : Prop :=
  (slot - tail).toNat < (head - tail).toNat
instance (head tail slot : BitVec 2) : Decidable (RingSlotOccupied head tail slot) :=
  inferInstanceAs (Decidable ((slot - tail).toNat < (head - tail).toNat))

/-- Every occupied next-state slot is newly written or was already occupied. -/
theorem queue_slot_transition_arithmetic : ∀ (head tail slot : BitVec 2) (enq deq : Bool),
    (head - tail).toNat ≤ 2 →
    (enq = true → head + 1 ≠ tail ∧ head + 2 ≠ tail) →
    (deq = true → head ≠ tail) →
    RingSlotOccupied (if enq then head + 1 else head)
      (if deq then tail + 1 else tail) slot →
    (enq = true ∧ slot = head) ∨ RingSlotOccupied head tail slot := by decide

def QueueSlotOccupied (s : State) (slot : BitVec 2) : Prop :=
  RingSlotOccupied s.g59.r1899_nringBufferHead s.g59.r1900_nringBufferTail slot

theorem queue_occupied_slot_step (s : State) (i : Inputs) (slot : BitVec 2)
    (reset : i.g0.nreset = 0) (flush : v30668 s i = 0)
    (bound : QueueOccupancy s ≤ 2) (occupied : QueueSlotOccupied (step s i) slot) :
    (v26198 s i = 1 ∧ slot = s.g59.r1899_nringBufferHead) ∨ QueueSlotOccupied s slot := by
  have arithmetic := queue_slot_transition_arithmetic s.g59.r1899_nringBufferHead
    s.g59.r1900_nringBufferTail slot (decide (v26198 s i = 1))
    (decide (v24283 s i = 1)) bound
    (by simpa using queue_enqueue_has_room s i)
    (by simpa using execute_capture_queue_nonempty s i)
  have target : RingSlotOccupied
      (if v26198 s i = 1 then s.g59.r1899_nringBufferHead + 1 else s.g59.r1899_nringBufferHead)
      (if v24283 s i = 1 then s.g59.r1900_nringBufferTail + 1 else s.g59.r1900_nringBufferTail) slot := by
    simpa only [QueueSlotOccupied, queue_head_step s i reset flush,
      queue_tail_step s i reset flush] using occupied
  simpa only [decide_eq_true_eq, QueueSlotOccupied] using arithmetic (by simpa using target)

theorem queue_tail_occupied_on_capture (s : State) (i : Inputs)
    (capture : v24283 s i = 1) : QueueSlotOccupied s s.g59.r1900_nringBufferTail := by
  have nonempty := execute_capture_queue_nonempty s i capture
  have fact : ∀ head tail : BitVec 2, head ≠ tail → RingSlotOccupied head tail tail := by decide
  exact fact _ _ nonempty

#print axioms queue_slot_transition_arithmetic
#print axioms queue_occupied_slot_step
#print axioms queue_tail_occupied_on_capture
end NutShellProofs
