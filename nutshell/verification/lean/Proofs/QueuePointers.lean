import Proofs.InstructionPCPipeline
namespace NutShellProofs
open nNutCore

theorem execute_capture_queue_nonempty (s : State) (i : Inputs)
    (capture : v24283 s i = 1) :
    s.g59.r1899_nringBufferHead ≠ s.g59.r1900_nringBufferTail := by
  intro empty
  simp [v24283, v11788, v11787, v11752, v11709, v11708, v11707, empty] at capture

theorem queue_pointers_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    (step s i).g59.r1899_nringBufferHead = 0 ∧
    (step s i).g59.r1900_nringBufferTail = 0 := by
  change v30676 s i = 0 ∧ v30705 s i = 0
  simp [v30676, v30705, reset, v4079]

theorem queue_pointers_flush (s : State) (i : Inputs) (flush : v30668 s i = 1) :
    (step s i).g59.r1899_nringBufferHead = 0 ∧
    (step s i).g59.r1900_nringBufferTail = 0 := by
  change v30676 s i = 0 ∧ v30705 s i = 0
  simp [v30676, v30705, v30675, v30704, flush, v30669, v30677, v4079]

theorem queue_enqueue_single (s : State) (i : Inputs) (enqueue : v26198 s i = 1) :
    v9827 s i = 1 ∧ v26201 s i = 1 := by
  rcases BitVec.eq_zero_or_eq_one (v9827 s i) with idle | valid
  · simp [v26198, v26197, v26193, v26192, v26191, v26190, v24,
      v26189, idle] at enqueue
  · constructor
    · exact valid
    · simp [v26201, v26199, v26200, v26193, v26192, v26191, v26190, v24, valid]

theorem queue_head_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (flush : v30668 s i = 0) :
    (step s i).g59.r1899_nringBufferHead =
      if v26198 s i = 1 then s.g59.r1899_nringBufferHead + 1
      else s.g59.r1899_nringBufferHead := by
  change v30676 s i = _
  by_cases enqueue : v26198 s i = 1
  · have count := (queue_enqueue_single s i enqueue).2
    simp [v30676, v30675, reset, flush, v30674, enqueue,
      v30673, v30672, v30671, v30670, count, v24,
      low_add _ _ (by decide : 2 ≤ 3),
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 2 ≤ 2)]
  · have idle : v26198 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right enqueue
    simp [v30676, v30675, reset, flush, v30674, idle]

theorem queue_tail_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (flush : v30668 s i = 0) :
    (step s i).g59.r1900_nringBufferTail =
      if v24283 s i = 1 then s.g59.r1900_nringBufferTail + 1
      else s.g59.r1900_nringBufferTail := by
  change v30705 s i = _
  have nonempty : v11708 s i = 0 → v11788 s i = 0 := by
    intro empty
    simp [v11788, v11787, v11752, v11709, empty]
  rcases BitVec.eq_zero_or_eq_one (v11708 s i) with empty | occupied
  · have idle := nonempty empty
    simp [v30678, v30679, v30680, v30681, v30682, v30683, v30684, v30685, v30686, v30687, v30688, v30689, v30690, v30691, v30692, v30693, v30694, v30695, v30696, v30697, v30698, v30699, v30700, v30701, v30702, v30703, v30704, v30705, reset, flush, v11709, v11706, v24283, empty, idle, v24]
  · rcases BitVec.eq_zero_or_eq_one (v11705 s i) with stalled | ready <;>
      rcases BitVec.eq_zero_or_eq_one (v11788 s i) with blocked | issue <;>
      simp_all [v30678, v30679, v30680, v30681, v30682, v30683, v30684, v30685, v30686, v30687, v30688, v30689, v30690, v30691, v30692, v30693, v30694, v30695, v30696, v30697, v30698, v30699, v30700, v30701, v30702, v30703, v30704, v30705, v11709, v11706, v24283, v24,
        low_add _ _ (by decide : 2 ≤ 3),
        BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 2 ≤ 2)]

#print axioms execute_capture_queue_nonempty
#print axioms queue_head_step
#print axioms queue_tail_step

theorem queue_enqueue_has_room (s : State) (i : Inputs) (enqueue : v26198 s i = 1) :
    s.g59.r1899_nringBufferHead + 1 ≠ s.g59.r1900_nringBufferTail ∧
    s.g59.r1899_nringBufferHead + 2 ≠ s.g59.r1900_nringBufferTail := by
  have valid := (queue_enqueue_single s i enqueue).1
  have ready : v9824 s i = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v9824 s i) with blocked | ready
    · simp [v26198, v26197, v26193, v26192, v26191, v26190,
        v24, v26189, v9830, v9829, v9828, valid, blocked] at enqueue
    · exact ready
  have addresses : v9817 s i = s.g59.r1899_nringBufferHead + 1 ∧
      v9822 s i = s.g59.r1899_nringBufferHead + 2 := by
    simp [v9817, v9816, v9815, v9814, v9822, v9821, v9820, v9819, v24,
      low_add _ _ (by decide : 2 ≤ 3),
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 2 ≤ 2)]
  constructor
  · intro full
    have same : v9817 s i = s.g59.r1900_nringBufferTail := addresses.1.trans full
    simp [v9824, v9818, same] at ready
  · intro full
    have same : v9822 s i = s.g59.r1900_nringBufferTail := addresses.2.trans full
    simp [v9824, v9823, same] at ready

#print axioms queue_enqueue_has_room
end NutShellProofs
