import Proofs.OccupiedInstructionPC
namespace NutShellProofs
open nNutCore

def RingSlots (head tail : BitVec 2) : List (BitVec 2) :=
  (List.range (head - tail).toNat).map (fun offset => tail + BitVec.ofNat 2 offset)

/-- None labels the new entry; Some labels an old slot. Finite kernel-checked ordering. -/
theorem queue_order_arithmetic : ∀ (head tail : BitVec 2) (enq deq : Bool),
    (head - tail).toNat ≤ 2 →
    (enq = true → head + 1 ≠ tail ∧ head + 2 ≠ tail) →
    (deq = true → head ≠ tail) →
    (RingSlots (if enq then head + 1 else head) (if deq then tail + 1 else tail)).map
      (fun slot => if enq = true ∧ slot = head then none else some slot) =
    (if deq then ((RingSlots head tail).map some).tail else (RingSlots head tail).map some) ++
      (if enq then [none] else []) := by decide

def QueueContents (s : State) : List (BitVec 64 × BitVec 39) :=
  (RingSlots s.g59.r1899_nringBufferHead s.g59.r1900_nringBufferTail).map (QueuePair s)

def IDUPair (s : State) : BitVec 64 × BitVec 39 :=
  (s.g38.r1242_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Finstr,
    s.g38.r1243_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpc)

theorem queue_contents_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (flush : v30668 s i = 0)
    (bound : QueueOccupancy s ≤ 2) :
    QueueContents (step s i) =
      (if v24283 s i = 1 then (QueueContents s).tail else QueueContents s) ++
      (if v26198 s i = 1 then [IDUPair s] else []) := by
  let decode : Option (BitVec 2) → BitVec 64 × BitVec 39 :=
    fun label => match label with | none => IDUPair s | some slot => QueuePair s slot
  have order := queue_order_arithmetic s.g59.r1899_nringBufferHead
    s.g59.r1900_nringBufferTail (decide (v26198 s i = 1)) (decide (v24283 s i = 1))
    bound (by simpa using queue_enqueue_has_room s i)
    (by simpa using execute_capture_queue_nonempty s i)
  have mapped := congrArg (List.map decode) order
  have data : ∀ slot, QueuePair (step s i) slot =
      decode (if v26198 s i = 1 ∧ slot = s.g59.r1899_nringBufferHead then none else some slot) := by
    intro slot
    rw [queue_pair_step s i slot reset]
    split <;> rfl
  simp only [QueueContents, queue_head_step s i reset flush, queue_tail_step s i reset flush]
  simp only [decide_eq_true_eq] at mapped
  rw [show QueuePair (step s i) = _ from funext data]
  rcases BitVec.eq_zero_or_eq_one (v26198 s i) with enq | enq <;>
    rcases BitVec.eq_zero_or_eq_one (v24283 s i) with deq | deq <;>
    simpa [enq, deq, List.map_map, Function.comp_def, decode] using mapped

theorem queue_contents_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    QueueContents (step s i) = [] := by
  rcases queue_pointers_reset s i reset with ⟨head, tail⟩
  simp [QueueContents, RingSlots, head, tail]

theorem queue_contents_flush (s : State) (i : Inputs) (flush : v30668 s i = 1) :
    QueueContents (step s i) = [] := by
  rcases queue_pointers_flush s i flush with ⟨head, tail⟩
  simp [QueueContents, RingSlots, head, tail]

#print axioms queue_order_arithmetic
#print axioms queue_contents_step

theorem queue_capture_is_front (s : State) (i : Inputs) (capture : v24283 s i = 1) :
    (QueueContents s).head? = some (v24297 s i, v24312 s i) := by
  have first : ∀ head tail : BitVec 2, head ≠ tail →
      (RingSlots head tail).head? = some tail := by decide
  have front := first _ _ (execute_capture_queue_nonempty s i capture)
  simp only [QueueContents, List.head?_map, front, Option.map_some]
  rw [queue_selected_pair]

/-- Abstract FIFO replay starting immediately after the initial reset. -/
def QueueReplay (initial : State) (inputs : Nat → Inputs) : Nat → List (BitVec 64 × BitVec 39)
  | 0 => []
  | t + 1 =>
    let s := run initial inputs (t + 1)
    let i := inputs (t + 1)
    if i.g0.nreset = 1 ∨ v30668 s i = 1 then [] else
      (if v24283 s i = 1 then (QueueReplay initial inputs t).tail else QueueReplay initial inputs t) ++
        (if v26198 s i = 1 then [IDUPair s] else [])

theorem queue_contents_replay (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    QueueContents (run initial inputs (t + 1)) = QueueReplay initial inputs t := by
  induction t with
  | zero => exact queue_contents_reset initial (inputs 0) reset
  | succ t ih =>
    rcases BitVec.eq_zero_or_eq_one (inputs (t + 1)).g0.nreset with noReset | activeReset
    · rcases BitVec.eq_zero_or_eq_one (v30668 (run initial inputs (t + 1)) (inputs (t + 1))) with noFlush | flush
      · have next := queue_contents_step _ _ noReset noFlush (queue_occupancy_bound_run initial inputs reset t)
        rw [ih] at next
        simpa [QueueReplay, noReset, noFlush] using next
      · have empty := queue_contents_flush (run initial inputs (t + 1)) (inputs (t + 1)) flush
        simpa [QueueReplay, noReset, flush] using empty
    · have empty := queue_contents_reset (run initial inputs (t + 1)) (inputs (t + 1)) activeReset
      simpa [QueueReplay, activeReset] using empty

theorem queue_capture_replay_front (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (capture : v24283 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    (QueueReplay initial inputs t).head? =
      some (v24297 (run initial inputs (t + 1)) (inputs (t + 1)),
        v24312 (run initial inputs (t + 1)) (inputs (t + 1))) := by
  rw [← queue_contents_replay initial inputs reset t]
  exact queue_capture_is_front _ _ capture

#print axioms queue_contents_replay
#print axioms queue_capture_replay_front
end NutShellProofs
