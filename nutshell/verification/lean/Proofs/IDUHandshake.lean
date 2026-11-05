import Proofs.QueueOrder
namespace NutShellProofs
open nNutCore

theorem idu_consume_is_enqueue (s : State) (i : Inputs) : v11097 s i = v26198 s i := by
  simp [v11097, v9831, v26198, v26189, v26197,
    v26193, v26192, v26191, v26190, v24, v9827]

theorem idu_capture_replaces_only_consumed (s : State) (i : Inputs)
    (valid : s.g38.r1241_nfrontend_5Fvalid = 1) (capture : v11102 s i = 1) :
    v26198 s i = 1 := by
  rcases BitVec.eq_zero_or_eq_one (v9830 s i) with blocked | ready
  · simp [v11102, v10044, v10043, v10042, v9813, v9812, v9811,
      v10041, v9833, v9832, v9831, v9825, valid, blocked, v24] at capture
  · simp [v26198, v26189, v26197, v26193, v26192, v26191, v26190,
      v9827, v9826, v9825, v9812, v9811, v24, valid, ready]

def IDUPending (s : State) : Option (BitVec 64 × BitVec 39) :=
  if s.g38.r1241_nfrontend_5Fvalid = 1 then some (IDUPair s) else none

theorem idu_pending_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    IDUPending (step s i) = none := by
  unfold IDUPending
  change (if v11101 s i = 1 then some (IDUPair (step s i)) else none) = none
  simp [v11101, v0, reset, v24]

theorem idu_pending_flush (s : State) (i : Inputs) (flush : v30668 s i = 1) :
    IDUPending (step s i) = none := by
  have iduFlush : v11095 s i = 1 := flush
  unfold IDUPending
  change (if v11101 s i = 1 then some (IDUPair (step s i)) else none) = none
  simp [v11101, v11100, iduFlush, v24]

theorem idu_pending_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (flush : v30668 s i = 0) :
    IDUPending (step s i) =
      if v11102 s i = 1 then some (v11105 s i, v10174 s i)
      else if v26198 s i = 1 then none else IDUPending s := by
  have iduFlush : v11095 s i = 0 := flush
  have sameCapture : v11096 s i = v11102 s i := rfl
  rcases BitVec.eq_zero_or_eq_one (v11102 s i) with hold | capture
  · rcases idu_instruction_pc_hold s i (by rw [hold]; decide) with ⟨instr, pc⟩
    have pair : IDUPair (step s i) = IDUPair s := by simp [IDUPair, instr, pc]
    unfold IDUPending
    change (if v11101 s i = 1 then some (IDUPair (step s i)) else none) = _
    rcases BitVec.eq_zero_or_eq_one (v26198 s i) with event | event <;>
      simp [v11101, v0, reset, v11100, iduFlush, v11099, sameCapture,
        hold, v11098, idu_consume_is_enqueue, event, v24, pair]
  · rcases idu_instruction_pc_capture s i capture with ⟨instr, pc⟩
    have pair : IDUPair (step s i) = (v11105 s i, v10174 s i) := by simp [IDUPair, instr, pc]
    unfold IDUPending
    change (if v11101 s i = 1 then some (IDUPair (step s i)) else none) = _
    simp [v11101, v0, reset, v11100, iduFlush, v11099, sameCapture, capture, v110, pair]

#print axioms idu_consume_is_enqueue
#print axioms idu_capture_replaces_only_consumed
#print axioms idu_pending_step

theorem idu_empty_cannot_enqueue (s : State) (i : Inputs) (empty : IDUPending s = none) :
    v26198 s i ≠ 1 := by
  intro enqueue
  have valid := (queue_enqueue_single s i enqueue).1
  change s.g38.r1241_nfrontend_5Fvalid = 1 at valid
  simp [IDUPending, valid] at empty

theorem idu_enqueue_consumes_without_capture (s : State) (i : Inputs)
    (enqueue : v26198 s i = 1) (noCapture : v11102 s i = 0) :
    IDUPending (step s i) = none := by
  rcases BitVec.eq_zero_or_eq_one i.g0.nreset with noReset | reset
  · rcases BitVec.eq_zero_or_eq_one (v30668 s i) with noFlush | flush
    · simp [idu_pending_step s i noReset noFlush, noCapture, enqueue]
    · exact idu_pending_flush s i flush
  · exact idu_pending_reset s i reset

theorem idu_empty_hold_without_capture (s : State) (i : Inputs)
    (empty : IDUPending s = none) (noCapture : v11102 s i = 0) :
    IDUPending (step s i) = none := by
  rcases BitVec.eq_zero_or_eq_one i.g0.nreset with noReset | reset
  · rcases BitVec.eq_zero_or_eq_one (v30668 s i) with noFlush | flush
    · simp [idu_pending_step s i noReset noFlush, noCapture, empty]
    · exact idu_pending_flush s i flush
  · exact idu_pending_reset s i reset

theorem idu_empty_until_capture (initial : State) (inputs : Nat → Inputs)
    (start count : Nat) (empty : IDUPending (run initial inputs start) = none)
    (quiet : ∀ k, k < count → v11102 (run initial inputs (start + k)) (inputs (start + k)) = 0) :
    IDUPending (run initial inputs (start + count)) = none := by
  induction count with
  | zero => simpa using empty
  | succ count ih =>
    have previous := ih (fun k hk => quiet k (by omega))
    exact idu_empty_hold_without_capture _ _ previous (quiet count (by omega))

theorem idu_no_reenqueue_before_new_capture (initial : State) (inputs : Nat → Inputs)
    (start count : Nat)
    (enqueue : v26198 (run initial inputs start) (inputs start) = 1)
    (quiet : ∀ k, k ≤ count → v11102 (run initial inputs (start + k)) (inputs (start + k)) = 0) :
    v26198 (run initial inputs (start + count + 1)) (inputs (start + count + 1)) ≠ 1 := by
  have empty : IDUPending (run initial inputs (start + 1)) = none :=
    idu_enqueue_consumes_without_capture _ _ enqueue (by simpa using quiet 0 (by omega))
  have held := idu_empty_until_capture initial inputs (start + 1) count empty
    (fun k hk => by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using quiet (k + 1) (by omega))
  apply idu_empty_cannot_enqueue
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using held

#print axioms idu_no_reenqueue_before_new_capture
end NutShellProofs
