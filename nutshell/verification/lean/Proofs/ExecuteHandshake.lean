import Proofs.FrontendPendingOrder
namespace NutShellProofs
open nNutCore

def EXUPair (s : State) : BitVec 64 × BitVec 39 :=
  (s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr,
    s.g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc)

def EXUPending (s : State) : Option (BitVec 64 × BitVec 39) :=
  if s.g47.r1511_nbackend_5Fvalid = 1 then some (EXUPair s) else none

theorem execute_completion_requires_valid (s : State) (i : Inputs)
    (complete : v11702 s i = 1) : s.g47.r1511_nbackend_5Fvalid = 1 := by
  rcases BitVec.eq_zero_or_eq_one s.g47.r1511_nbackend_5Fvalid with idle | valid
  · simp [v11702, v11701, v6, idle] at complete
  · exact valid

theorem execute_capture_replaces_only_completed (s : State) (i : Inputs)
    (valid : s.g47.r1511_nbackend_5Fvalid = 1) (capture : v24283 s i = 1) :
    v11702 s i = 1 := by
  rcases BitVec.eq_zero_or_eq_one (v11702 s i) with stalled | complete
  · simp [v24283, v11705, v11704, v11491, v6, valid,
      v24, v11703, stalled] at capture
  · exact complete

theorem execute_pending_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    EXUPending (step s i) = none := by
  have clear := execute_valid_reset s i i reset
  change (step s i).g47.r1511_nbackend_5Fvalid = 0 at clear
  simp [EXUPending, clear]

theorem execute_pending_flush (s : State) (i : Inputs) (flush : v24276 s i = 1) :
    EXUPending (step s i) = none := by
  unfold EXUPending
  change (if v24282 s i = 1 then some (EXUPair (step s i)) else none) = none
  simp [v24282, v24281, flush, v24]

theorem execute_pending_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (flush : v24276 s i = 0) :
    EXUPending (step s i) =
      if v24283 s i = 1 then some (v24297 s i, v24312 s i)
      else if v11702 s i = 1 then none else EXUPending s := by
  have sameCapture : v24277 s i = v24283 s i := rfl
  have consume : v24278 s i = v11702 s i := by
    rcases BitVec.eq_zero_or_eq_one (v11702 s i) with value | value <;>
      simp [v24278, v11493, v11492, v110, value]
  have pair : EXUPair (step s i) =
      if v24283 s i = 1 then (v24297 s i, v24312 s i) else EXUPair s := by
    unfold EXUPair
    change (v24298 s i, v24313 s i) = _
    by_cases capture : v24283 s i = 1
    · rw [v24298, v24313, if_pos capture, if_pos capture, if_pos capture]
    · rw [v24298, v24313, if_neg capture, if_neg capture, if_neg capture]
  unfold EXUPending
  change (if v24282 s i = 1 then some (EXUPair (step s i)) else none) = _
  rcases BitVec.eq_zero_or_eq_one (v24283 s i) with capture | capture <;>
    rcases BitVec.eq_zero_or_eq_one (v11702 s i) with complete | complete <;>
    simp [v24282, v11455, reset, v24281, flush, v24280, sameCapture,
      capture, v24279, consume, complete, v24, v110, pair]

theorem next_commit_is_execute_completion (s : State) (i next : Inputs)
    (reset : i.g0.nreset = 0) (flush : v25328 s i = 0) :
    v9 (step s i) next = v11702 s i := by
  change v25331 s i = _
  rcases BitVec.eq_zero_or_eq_one (v11702 s i) with complete | complete <;>
    simp [v25331, v11455, reset, v25330, flush, v25329, v11492, v110, complete]

#print axioms execute_capture_replaces_only_completed
#print axioms execute_pending_step
#print axioms next_commit_is_execute_completion

theorem execute_empty_cannot_complete (s : State) (i : Inputs) (empty : EXUPending s = none) :
    v11702 s i ≠ 1 := by
  intro complete
  have valid := execute_completion_requires_valid s i complete
  simp [EXUPending, valid] at empty

theorem execute_complete_consumes_without_capture (s : State) (i : Inputs)
    (complete : v11702 s i = 1) (noCapture : v24283 s i = 0) :
    EXUPending (step s i) = none := by
  rcases BitVec.eq_zero_or_eq_one i.g0.nreset with noReset | reset
  · rcases BitVec.eq_zero_or_eq_one (v24276 s i) with noFlush | flush
    · simp [execute_pending_step s i noReset noFlush, noCapture, complete]
    · exact execute_pending_flush s i flush
  · exact execute_pending_reset s i reset

theorem execute_empty_hold_without_capture (s : State) (i : Inputs)
    (empty : EXUPending s = none) (noCapture : v24283 s i = 0) :
    EXUPending (step s i) = none := by
  rcases BitVec.eq_zero_or_eq_one i.g0.nreset with noReset | reset
  · rcases BitVec.eq_zero_or_eq_one (v24276 s i) with noFlush | flush
    · simp [execute_pending_step s i noReset noFlush, noCapture, empty]
    · exact execute_pending_flush s i flush
  · exact execute_pending_reset s i reset

theorem execute_empty_until_capture (initial : State) (inputs : Nat → Inputs)
    (start count : Nat) (empty : EXUPending (run initial inputs start) = none)
    (quiet : ∀ k, k < count → v24283 (run initial inputs (start + k)) (inputs (start + k)) = 0) :
    EXUPending (run initial inputs (start + count)) = none := by
  induction count with
  | zero => simpa using empty
  | succ count ih =>
    have previous := ih (fun k hk => quiet k (by omega))
    exact execute_empty_hold_without_capture _ _ previous (quiet count (by omega))

theorem execute_no_recompletion_before_new_capture (initial : State) (inputs : Nat → Inputs)
    (start count : Nat)
    (complete : v11702 (run initial inputs start) (inputs start) = 1)
    (quiet : ∀ k, k ≤ count → v24283 (run initial inputs (start + k)) (inputs (start + k)) = 0) :
    v11702 (run initial inputs (start + count + 1)) (inputs (start + count + 1)) ≠ 1 := by
  have empty : EXUPending (run initial inputs (start + 1)) = none :=
    execute_complete_consumes_without_capture _ _ complete (by simpa using quiet 0 (by omega))
  have held := execute_empty_until_capture initial inputs (start + 1) count empty
    (fun k hk => by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using quiet (k + 1) (by omega))
  apply execute_empty_cannot_complete
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using held

#print axioms execute_no_recompletion_before_new_capture
end NutShellProofs
