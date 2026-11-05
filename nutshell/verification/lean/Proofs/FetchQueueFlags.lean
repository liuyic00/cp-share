import Proofs.FetchQueuePCOrder
namespace NutShellProofs
open nNutCore

def FetchSlotFlags (s : State) (slot : BitVec 2) : BitVec 4 :=
  if slot = 0 then s.g34.r1116_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F0_5FbrIdx
  else if slot = 1 then s.g36.r1155_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F1_5FbrIdx
  else if slot = 2 then s.g37.r1194_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F2_5FbrIdx
  else s.g38.r1233_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F3_5FbrIdx

def FetchFlagContents (s : State) : List (BitVec 4) :=
  (FetchRingSlots s.g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue
    s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue
    (decide (s.g38.r1240_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fmaybe_5Ffull = 1))).map (FetchSlotFlags s)

theorem fetch_slot_flags_step (s : State) (i : Inputs) (slot : BitVec 2)
    (reset : i.g0.nreset = 0) :
    FetchSlotFlags (step s i) slot =
      if v10241 s i = 1 ∧ slot = s.g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue
      then v10501 s i else FetchSlotFlags s slot := by
  have bound := slot.isLt
  have cases : slot.toNat = 0 ∨ slot.toNat = 1 ∨ slot.toNat = 2 ∨ slot.toNat = 3 := by omega
  rcases cases with c | c | c | c
  · have value : slot = (0 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    subst slot
    unfold FetchSlotFlags
    change (if (0 : BitVec 2) = 0 then v10504 s i else if (0 : BitVec 2) = 1 then v10707 s i else if (0 : BitVec 2) = 2 then v10867 s i else v11023 s i) = _
    by_cases enqueue : v10241 s i = BitVec.ofNat 1 1
    all_goals simp [enqueue, v10504, v10503, v10502, v10498, v10497, v10235, v0, reset]
  · have value : slot = (1 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    subst slot
    unfold FetchSlotFlags
    change (if (1 : BitVec 2) = 0 then v10504 s i else if (1 : BitVec 2) = 1 then v10707 s i else if (1 : BitVec 2) = 2 then v10867 s i else v11023 s i) = _
    by_cases enqueue : v10241 s i = BitVec.ofNat 1 1
    all_goals simp [enqueue, v10707, v10706, v10705, v10704, v10703, v10235, v0, reset]
  · have value : slot = (2 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    subst slot
    unfold FetchSlotFlags
    change (if (2 : BitVec 2) = 0 then v10504 s i else if (2 : BitVec 2) = 1 then v10707 s i else if (2 : BitVec 2) = 2 then v10867 s i else v11023 s i) = _
    by_cases enqueue : v10241 s i = BitVec.ofNat 1 1
    all_goals simp [enqueue, v10867, v10866, v10865, v10864, v9721, v10235, v0, reset]
  · have value : slot = (3 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    subst slot
    unfold FetchSlotFlags
    change (if (3 : BitVec 2) = 0 then v10504 s i else if (3 : BitVec 2) = 1 then v10707 s i else if (3 : BitVec 2) = 2 then v10867 s i else v11023 s i) = _
    by_cases enqueue : v10241 s i = BitVec.ofNat 1 1
    all_goals simp [enqueue, v11023, v11022, v11021, v11020, v2750, v10235, v0, reset]

theorem fetch_flags_contents_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (flush : v14 s i = 0) :
    FetchFlagContents (step s i) =
      (if v11083 s i = 1 then (FetchFlagContents s).tail else FetchFlagContents s) ++
      (if v10241 s i = 1 then [v10501 s i] else []) := by
  let decode : Option (BitVec 2) → BitVec 4 :=
    fun label => match label with | none => v10501 s i | some slot => FetchSlotFlags s slot
  have order := fetch_ring_order_arithmetic
    s.g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue
    s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue
    (decide (s.g38.r1240_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fmaybe_5Ffull = 1))
    (decide (v10241 s i = 1)) (decide (v11083 s i = 1))
    (by simpa using fetch_enqueue_not_full s i)
    (by simpa using fetch_dequeue_not_empty s i)
  have mapped := congrArg (List.map decode) order
  have data : ∀ slot, FetchSlotFlags (step s i) slot =
      decode (if v10241 s i = 1 ∧ slot = s.g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue
        then none else some slot) := by
    intro slot
    rw [fetch_slot_flags_step s i slot reset]
    split <;> rfl
  have tail : (step s i).g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue =
      if v11083 s i = 1 then s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue + 1
      else s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue := by
    change v11090 s i = _
    simp [v11090, v10235, v0, reset, v11089, v11041, v11040, v18, v17,
      flush, v16, v11088, v11087, v11086, v11084, v11085,
      low_add _ _ (by decide : 2 ≤ 3),
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 2 ≤ 2)]
  simp only [FetchFlagContents, fetch_enqueue_pointer_step s i reset flush,
    tail, fetch_full_bit_step s i reset flush]
  rw [show FetchSlotFlags (step s i) = _ from funext data]
  rcases BitVec.eq_zero_or_eq_one (v10241 s i) with enq | enq <;>
    rcases BitVec.eq_zero_or_eq_one (v11083 s i) with deq | deq <;>
    rcases BitVec.eq_zero_or_eq_one s.g38.r1240_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fmaybe_5Ffull with full | full <;>
    simpa [enq, deq, full, List.map_map, Function.comp_def, decode] using mapped

theorem fetch_flags_contents_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    FetchFlagContents (step s i) = [] := by
  have head : (step s i).g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue = 0 := by
    change v11049 s i = 0
    simp [v11049, v10235, v0, reset, v11048, v11041, v11040, v18, v17, v15, v11042, v4079]
  have tail : (step s i).g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = 0 := by
    change v11090 s i = 0
    simp [v11090, v10235, v0, reset, v11089, v11041, v11040, v18, v17, v15, v11050, v4079]
  have full : (step s i).g38.r1240_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fmaybe_5Ffull = 0 := by
    change v11094 s i = 0
    simp [v11094, v10235, v0, reset, v11093, v11041, v11040, v18, v17, v15, v24]
  simp [FetchFlagContents, head, tail, full, FetchRingSlots]

theorem fetch_flags_contents_flush (s : State) (i : Inputs) (flush : v14 s i = 1) :
    FetchFlagContents (step s i) = [] := by
  have head : (step s i).g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue = 0 := by
    change v11049 s i = 0
    simp [v11049, v10235, v0, flush, v11048, v11041, v11040, v18, v17, v15, v11042, v4079]
  have tail : (step s i).g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = 0 := by
    change v11090 s i = 0
    simp [v11090, v10235, v0, flush, v11089, v11041, v11040, v18, v17, v15, v11050, v4079]
  have full : (step s i).g38.r1240_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fmaybe_5Ffull = 0 := by
    change v11094 s i = 0
    simp [v11094, v10235, v0, flush, v11093, v11041, v11040, v18, v17, v15, v24]
  simp [FetchFlagContents, head, tail, full, FetchRingSlots]

theorem fetch_flags_selected_slot (s : State) (i : Inputs) :
    v9795 s i = FetchSlotFlags s s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue := by
  have bound := s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue.isLt
  have cases : s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue.toNat = 0 ∨ s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue.toNat = 1 ∨ s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue.toNat = 2 ∨ s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue.toNat = 3 := by omega
  rcases cases with c | c | c | c
  · have ptr : s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = (0 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simp [FetchSlotFlags, v9795, v9794, v9793, v9792, v9791, v9790, v9789, v9788, v9787, v9786, v9785, v9784, v9721, v9783, v2750, v110, ptr]
  · have ptr : s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = (1 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simp [FetchSlotFlags, v9795, v9794, v9793, v9792, v9791, v9790, v9789, v9788, v9787, v9786, v9785, v9784, v9721, v9783, v2750, v110, ptr]
  · have ptr : s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = (2 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simp [FetchSlotFlags, v9795, v9794, v9793, v9792, v9791, v9790, v9789, v9788, v9787, v9786, v9785, v9784, v9721, v9783, v2750, v110, ptr]
  · have ptr : s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = (3 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simp [FetchSlotFlags, v9795, v9794, v9793, v9792, v9791, v9790, v9789, v9788, v9787, v9786, v9785, v9784, v9721, v9783, v2750, v110, ptr]

theorem fetch_flags_dequeue_is_front (s : State) (i : Inputs) (dequeue : v11083 s i = 1) :
    (FetchFlagContents s).head? = some (v9795 s i) := by
  have first : ∀ (head tail : BitVec 2) (full : Bool),
      (head ≠ tail ∨ full = true) → (FetchRingSlots head tail full).head? = some tail := by decide
  have selected := first s.g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue
    s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue
    (decide (s.g38.r1240_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fmaybe_5Ffull = 1))
    (by simpa using fetch_dequeue_not_empty s i dequeue)
  rw [FetchFlagContents, List.head?_map, selected]
  exact congrArg some (fetch_flags_selected_slot s i).symm

#print axioms fetch_flags_dequeue_is_front
#print axioms fetch_flags_contents_reset
#print axioms fetch_flags_contents_flush
#print axioms fetch_flags_contents_step
#print axioms fetch_slot_flags_step

theorem temporary_pc32_fetch_flags_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) :
    ∀ flags ∈ FetchFlagContents (run initial inputs (t + 1)), flags = 8 := by
  induction t with
  | zero =>
    change ∀ flags ∈ FetchFlagContents (step initial (inputs 0)), flags = 8
    simp [fetch_flags_contents_reset _ _ reset]
  | succ t ih =>
    rcases BitVec.eq_zero_or_eq_one (inputs (t + 1)).g0.nreset with normal | resetting
    · rcases BitVec.eq_zero_or_eq_one (v14 (run initial inputs (t + 1)) (inputs (t + 1))) with noFlush | flush
      · change ∀ flags ∈ FetchFlagContents (step (run initial inputs (t + 1)) (inputs (t + 1))), flags = 8
        rw [fetch_flags_contents_step _ _ normal noFlush]
        intro flags member
        rcases List.mem_append.mp member with old | fresh
        · split at old
          · exact ih flags (List.mem_of_mem_tail old)
          · exact ih flags old
        · split at fresh
          · rename_i enqueue
            have same : flags = v10501 (run initial inputs (t + 1)) (inputs (t + 1)) := by simpa using fresh
            exact same.trans (temporary_pc32_fetch_enqueue_metadata_run initial inputs reset environment restriction t enqueue).2
          · simp at fresh
      · change ∀ flags ∈ FetchFlagContents (step (run initial inputs (t + 1)) (inputs (t + 1))), flags = 8
        simp [fetch_flags_contents_flush _ _ flush]
    · change ∀ flags ∈ FetchFlagContents (step (run initial inputs (t + 1)) (inputs (t + 1))), flags = 8
      simp [fetch_flags_contents_reset _ _ resetting]

theorem temporary_pc32_fetch_dequeue_successor (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (dequeue : v11083 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    v10194 (run initial inputs (t + 1)) (inputs (t + 1)) =
      v9733 (run initial inputs (t + 1)) (inputs (t + 1)) + 4 := by
  have head := fetch_flags_dequeue_is_front _ _ dequeue
  have member := List.mem_of_head? head
  have marked := temporary_pc32_fetch_flags_run initial inputs reset environment restriction t _ member
  rcases fetch_queue_sequential_selected _ _
    (temporary_pc32_fetch_queue_sequential_run initial inputs reset environment restriction t) with zero | good
  · rw [marked] at zero
    contradiction
  · exact good.2

#print axioms temporary_pc32_fetch_flags_run
#print axioms temporary_pc32_fetch_dequeue_successor

theorem frontend_sequential_prediction (s : State) (i : Inputs)
    (state : s.g33.r1072_nfrontend_5Fibf_5Fstate = 0)
    (noRedirect : v14 s i = 0)
    (full : v9780 s i = 0)
    (successor : v10194 s i = v9733 s i + 4) :
    v11139 s i = v10174 s i + 4 := by
  rw [frontend_word_output_pc s i state noRedirect]
  have plusFour : v11118 s i = v9733 s i + 4 := by
    simp [v11118, full, v11117, v11116, v11114, v11115,
      low_add _ _ (by decide : 39 ≤ 40),
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 39 ≤ 39)]
  simp [v11139, v11138, v11109, v9717, v9716, v9715, v18, v17,
    noRedirect, v16, v24, v110, v11137, v9718, v4079, state,
    v11119, successor, plusFour]

theorem temporary_pc32_idu_capture_prediction (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (currentReset : (inputs (t + 1)).g0.nreset = 0)
    (noRedirect : v14 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (capture : v11102 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    v11139 (run initial inputs (t + 1)) (inputs (t + 1)) =
      v10174 (run initial inputs (t + 1)) (inputs (t + 1)) + 4 := by
  have valid : v10100 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 := by
    change v10100 _ _ &&& v10044 _ _ = 1 at capture
    exact (BitVec.and_eq_allOnes_iff.mp capture).1
  exact frontend_sequential_prediction _ _
    (temporary_pc32_frontend_word_state_run initial inputs reset environment restriction t) noRedirect
    (original_assumptions_disable_compressed_output _ _ (environment (t + 1)) currentReset valid)
    (temporary_pc32_fetch_dequeue_successor initial inputs reset environment restriction t
      ((temporary_pc32_dequeue_eq_capture_run initial inputs reset environment restriction t currentReset noRedirect).trans capture))

#print axioms temporary_pc32_idu_capture_prediction
end NutShellProofs
