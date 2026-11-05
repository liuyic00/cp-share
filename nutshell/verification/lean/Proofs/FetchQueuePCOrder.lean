import Proofs.FetchQueueControl
namespace NutShellProofs
open nNutCore

def FetchSlotPC (s : State) (slot : BitVec 2) : BitVec 39 :=
  if slot = 0 then s.g33.r1083_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F0_5Fpc
  else if slot = 1 then s.g35.r1122_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F1_5Fpc
  else if slot = 2 then s.g36.r1161_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F2_5Fpc
  else s.g37.r1200_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F3_5Fpc

def FetchPCContents (s : State) : List (BitVec 39) :=
  (FetchRingSlots s.g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue
    s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue
    (decide (s.g38.r1240_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fmaybe_5Ffull = 1))).map (FetchSlotPC s)

theorem fetch_slot_pc_step (s : State) (i : Inputs) (slot : BitVec 2)
    (reset : i.g0.nreset = 0) :
    FetchSlotPC (step s i) slot =
      if v10241 s i = 1 ∧ slot = s.g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue
      then v10265 s i else FetchSlotPC s slot := by
  have bound := slot.isLt
  have cases : slot.toNat = 0 ∨ slot.toNat = 1 ∨ slot.toNat = 2 ∨ slot.toNat = 3 := by omega
  rcases cases with c | c | c | c
  · have value : slot = (0 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    subst slot
    unfold FetchSlotPC
    change (if (0 : BitVec 2) = 0 then v10268 s i else if (0 : BitVec 2) = 1 then v10542 s i else if (0 : BitVec 2) = 2 then v10735 s i else v10891 s i) = _
    by_cases enqueue : v10241 s i = BitVec.ofNat 1 1
    all_goals simp [enqueue, v10268, v10267, v10266, v10256, v10255, v10235, v0, reset]
  · have value : slot = (1 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    subst slot
    unfold FetchSlotPC
    change (if (1 : BitVec 2) = 0 then v10268 s i else if (1 : BitVec 2) = 1 then v10542 s i else if (1 : BitVec 2) = 2 then v10735 s i else v10891 s i) = _
    by_cases enqueue : v10241 s i = BitVec.ofNat 1 1
    all_goals simp [enqueue, v10542, v10541, v10540, v10539, v10538, v10235, v0, reset]
  · have value : slot = (2 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    subst slot
    unfold FetchSlotPC
    change (if (2 : BitVec 2) = 0 then v10268 s i else if (2 : BitVec 2) = 1 then v10542 s i else if (2 : BitVec 2) = 2 then v10735 s i else v10891 s i) = _
    by_cases enqueue : v10241 s i = BitVec.ofNat 1 1
    all_goals simp [enqueue, v10735, v10734, v10733, v10732, v9721, v10235, v0, reset]
  · have value : slot = (3 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    subst slot
    unfold FetchSlotPC
    change (if (3 : BitVec 2) = 0 then v10268 s i else if (3 : BitVec 2) = 1 then v10542 s i else if (3 : BitVec 2) = 2 then v10735 s i else v10891 s i) = _
    by_cases enqueue : v10241 s i = BitVec.ofNat 1 1
    all_goals simp [enqueue, v10891, v10890, v10889, v10888, v2750, v10235, v0, reset]

theorem fetch_pc_contents_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (flush : v14 s i = 0) :
    FetchPCContents (step s i) =
      (if v11083 s i = 1 then (FetchPCContents s).tail else FetchPCContents s) ++
      (if v10241 s i = 1 then [v10265 s i] else []) := by
  let decode : Option (BitVec 2) → BitVec 39 :=
    fun label => match label with | none => v10265 s i | some slot => FetchSlotPC s slot
  have order := fetch_ring_order_arithmetic
    s.g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue
    s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue
    (decide (s.g38.r1240_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fmaybe_5Ffull = 1))
    (decide (v10241 s i = 1)) (decide (v11083 s i = 1))
    (by simpa using fetch_enqueue_not_full s i)
    (by simpa using fetch_dequeue_not_empty s i)
  have mapped := congrArg (List.map decode) order
  have data : ∀ slot, FetchSlotPC (step s i) slot =
      decode (if v10241 s i = 1 ∧ slot = s.g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue
        then none else some slot) := by
    intro slot
    rw [fetch_slot_pc_step s i slot reset]
    split <;> rfl
  have tail : (step s i).g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue =
      if v11083 s i = 1 then s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue + 1
      else s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue := by
    change v11090 s i = _
    simp [v11090, v10235, v0, reset, v11089, v11041, v11040, v18, v17,
      flush, v16, v11088, v11087, v11086, v11084, v11085,
      low_add _ _ (by decide : 2 ≤ 3),
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 2 ≤ 2)]
  simp only [FetchPCContents, fetch_enqueue_pointer_step s i reset flush,
    tail, fetch_full_bit_step s i reset flush]
  rw [show FetchSlotPC (step s i) = _ from funext data]
  rcases BitVec.eq_zero_or_eq_one (v10241 s i) with enq | enq <;>
    rcases BitVec.eq_zero_or_eq_one (v11083 s i) with deq | deq <;>
    rcases BitVec.eq_zero_or_eq_one s.g38.r1240_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fmaybe_5Ffull with full | full <;>
    simpa [enq, deq, full, List.map_map, Function.comp_def, decode] using mapped

theorem fetch_pc_contents_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    FetchPCContents (step s i) = [] := by
  have head : (step s i).g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue = 0 := by
    change v11049 s i = 0
    simp [v11049, v10235, v0, reset, v11048, v11041, v11040, v18, v17, v15, v11042, v4079]
  have tail : (step s i).g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = 0 := by
    change v11090 s i = 0
    simp [v11090, v10235, v0, reset, v11089, v11041, v11040, v18, v17, v15, v11050, v4079]
  have full : (step s i).g38.r1240_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fmaybe_5Ffull = 0 := by
    change v11094 s i = 0
    simp [v11094, v10235, v0, reset, v11093, v11041, v11040, v18, v17, v15, v24]
  simp [FetchPCContents, head, tail, full, FetchRingSlots]

theorem fetch_pc_contents_flush (s : State) (i : Inputs) (flush : v14 s i = 1) :
    FetchPCContents (step s i) = [] := by
  have head : (step s i).g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue = 0 := by
    change v11049 s i = 0
    simp [v11049, v10235, v0, flush, v11048, v11041, v11040, v18, v17, v15, v11042, v4079]
  have tail : (step s i).g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = 0 := by
    change v11090 s i = 0
    simp [v11090, v10235, v0, flush, v11089, v11041, v11040, v18, v17, v15, v11050, v4079]
  have full : (step s i).g38.r1240_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fmaybe_5Ffull = 0 := by
    change v11094 s i = 0
    simp [v11094, v10235, v0, flush, v11093, v11041, v11040, v18, v17, v15, v24]
  simp [FetchPCContents, head, tail, full, FetchRingSlots]

theorem fetch_pc_selected_slot (s : State) (i : Inputs) :
    v9733 s i = FetchSlotPC s s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue := by
  have bound := s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue.isLt
  have cases : s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue.toNat = 0 ∨ s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue.toNat = 1 ∨ s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue.toNat = 2 ∨ s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue.toNat = 3 := by omega
  rcases cases with c | c | c | c
  · have ptr : s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = (0 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simp [FetchSlotPC, v9733, v9732, v9731, v9730, v9729, v9728, v9727, v9726, v9725, v9724, v9723, v9722, v9721, v9720, v2750, v110, ptr]
  · have ptr : s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = (1 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simp [FetchSlotPC, v9733, v9732, v9731, v9730, v9729, v9728, v9727, v9726, v9725, v9724, v9723, v9722, v9721, v9720, v2750, v110, ptr]
  · have ptr : s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = (2 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simp [FetchSlotPC, v9733, v9732, v9731, v9730, v9729, v9728, v9727, v9726, v9725, v9724, v9723, v9722, v9721, v9720, v2750, v110, ptr]
  · have ptr : s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = (3 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simp [FetchSlotPC, v9733, v9732, v9731, v9730, v9729, v9728, v9727, v9726, v9725, v9724, v9723, v9722, v9721, v9720, v2750, v110, ptr]

theorem fetch_pc_dequeue_is_front (s : State) (i : Inputs) (dequeue : v11083 s i = 1) :
    (FetchPCContents s).head? = some (v9733 s i) := by
  have first : ∀ (head tail : BitVec 2) (full : Bool),
      (head ≠ tail ∨ full = true) → (FetchRingSlots head tail full).head? = some tail := by decide
  have selected := first s.g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue
    s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue
    (decide (s.g38.r1240_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fmaybe_5Ffull = 1))
    (by simpa using fetch_dequeue_not_empty s i dequeue)
  rw [FetchPCContents, List.head?_map, selected]
  exact congrArg some (fetch_pc_selected_slot s i).symm

#print axioms fetch_pc_dequeue_is_front
#print axioms fetch_pc_contents_reset
#print axioms fetch_pc_contents_flush
#print axioms fetch_pc_contents_step
#print axioms fetch_slot_pc_step
end NutShellProofs
