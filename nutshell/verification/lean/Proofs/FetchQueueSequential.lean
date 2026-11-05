import Proofs.FetchResponseMetadata
namespace NutShellProofs
open nNutCore

/-- Reset slots may have flag zero; sequentially written slots carry their exact successor. -/
def FetchSlotSequential (pc nextPC : BitVec 39) (flags : BitVec 4) : Prop :=
  flags = 0 ∨ (flags = 8 ∧ nextPC = pc + 4)

def FetchQueueSequential (s : State) : Prop :=
  FetchSlotSequential s.g33.r1083_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F0_5Fpc s.g33.r1084_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F0_5Fpnpc s.g34.r1116_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F0_5FbrIdx ∧
  FetchSlotSequential s.g35.r1122_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F1_5Fpc s.g35.r1123_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F1_5Fpnpc s.g36.r1155_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F1_5FbrIdx ∧
  FetchSlotSequential s.g36.r1161_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F2_5Fpc s.g36.r1162_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F2_5Fpnpc s.g37.r1194_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F2_5FbrIdx ∧
  FetchSlotSequential s.g37.r1200_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F3_5Fpc s.g37.r1201_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F3_5Fpnpc s.g38.r1233_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F3_5FbrIdx

theorem fetch_queue_sequential_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    FetchQueueSequential (step s i) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change FetchSlotSequential (v10268 s i) (v10276 s i) (v10504 s i)
    left
    simp [v10504, v10235, v0, reset, v8317]
  · change FetchSlotSequential (v10542 s i) (v10547 s i) (v10707 s i)
    left
    simp [v10707, v10235, v0, reset, v8317]
  · change FetchSlotSequential (v10735 s i) (v10739 s i) (v10867 s i)
    left
    simp [v10867, v10235, v0, reset, v8317]
  · change FetchSlotSequential (v10891 s i) (v10895 s i) (v11023 s i)
    left
    simp [v11023, v10235, v0, reset, v8317]

theorem fetch_queue_sequential_step (s : State) (i : Inputs)
    (old : FetchQueueSequential s)
    (incoming : v10241 s i = 1 → v10273 s i = v10265 s i + 4 ∧ v10501 s i = 8) :
    FetchQueueSequential (step s i) := by
  rcases old with ⟨h0,h1,h2,h3⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · change FetchSlotSequential (v10268 s i) (v10276 s i) (v10504 s i)
    by_cases reset : v10235 s i = BitVec.ofNat 1 1
    all_goals by_cases enqueue : v10241 s i = BitVec.ofNat 1 1
    all_goals by_cases selected : BitVec.ofNat 2 0 = s.g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue
    all_goals simp_all [FetchSlotSequential, v10268, v10267, v10266, v10256, v10255, v10276, v10275, v10274, v10270, v10269, v10504, v10503, v10502, v10498, v10497, v8317]
  · change FetchSlotSequential (v10542 s i) (v10547 s i) (v10707 s i)
    by_cases reset : v10235 s i = BitVec.ofNat 1 1
    all_goals by_cases enqueue : v10241 s i = BitVec.ofNat 1 1
    all_goals by_cases selected : BitVec.ofNat 2 1 = s.g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue
    all_goals simp_all [FetchSlotSequential, v10542, v10541, v10540, v10539, v10538, v10547, v10546, v10545, v10544, v10543, v10707, v10706, v10705, v10704, v10703, v8317]
  · change FetchSlotSequential (v10735 s i) (v10739 s i) (v10867 s i)
    by_cases reset : v10235 s i = BitVec.ofNat 1 1
    all_goals by_cases enqueue : v10241 s i = BitVec.ofNat 1 1
    all_goals by_cases selected : BitVec.ofNat 2 2 = s.g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue
    all_goals simp_all [FetchSlotSequential, v10735, v10734, v10733, v10732, v9721, v10739, v10738, v10737, v10736, v10867, v10866, v10865, v10864, v8317]
  · change FetchSlotSequential (v10891 s i) (v10895 s i) (v11023 s i)
    by_cases reset : v10235 s i = BitVec.ofNat 1 1
    all_goals by_cases enqueue : v10241 s i = BitVec.ofNat 1 1
    all_goals by_cases selected : BitVec.ofNat 2 3 = s.g38.r1238_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fenq_5Fptr_5Fvalue
    all_goals simp_all [FetchSlotSequential, v10891, v10890, v10889, v10888, v2750, v10895, v10894, v10893, v10892, v11023, v11022, v11021, v11020, v8317]

theorem temporary_pc32_fetch_queue_sequential_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) :
    FetchQueueSequential (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact fetch_queue_sequential_reset _ _ reset
  | succ t ih =>
    exact fetch_queue_sequential_step _ _ ih
      (temporary_pc32_fetch_enqueue_metadata_run initial inputs reset environment restriction t)

theorem fetch_queue_sequential_selected (s : State) (i : Inputs)
    (old : FetchQueueSequential s) :
    FetchSlotSequential (v9733 s i) (v10194 s i) (v9795 s i) := by
  rcases old with ⟨h0,h1,h2,h3⟩
  have bound := s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue.isLt
  have cases : s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue.toNat = 0 ∨ s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue.toNat = 1 ∨ s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue.toNat = 2 ∨ s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue.toNat = 3 := by omega
  rcases cases with c | c | c | c
  · have ptr : s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = (0 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v9733, v9732, v9731, v9720, v2750, v9730, v9722, v9721, v9729, v9724, v9723, v9728, v9727, v9726, v9725, v110, v10194, v10193, v10192, v10182, v10191, v10183, v10190, v10185, v10184, v10189, v10188, v10187, v10186, v9795, v9794, v9793, v9783, v9792, v9784, v9791, v9786, v9785, v9790, v9789, v9788, v9787, ptr] using h0
  · have ptr : s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = (1 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v9733, v9732, v9731, v9720, v2750, v9730, v9722, v9721, v9729, v9724, v9723, v9728, v9727, v9726, v9725, v110, v10194, v10193, v10192, v10182, v10191, v10183, v10190, v10185, v10184, v10189, v10188, v10187, v10186, v9795, v9794, v9793, v9783, v9792, v9784, v9791, v9786, v9785, v9790, v9789, v9788, v9787, ptr] using h1
  · have ptr : s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = (2 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v9733, v9732, v9731, v9720, v2750, v9730, v9722, v9721, v9729, v9724, v9723, v9728, v9727, v9726, v9725, v110, v10194, v10193, v10192, v10182, v10191, v10183, v10190, v10185, v10184, v10189, v10188, v10187, v10186, v9795, v9794, v9793, v9783, v9792, v9784, v9791, v9786, v9785, v9790, v9789, v9788, v9787, ptr] using h2
  · have ptr : s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = (3 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [v9733, v9732, v9731, v9720, v2750, v9730, v9722, v9721, v9729, v9724, v9723, v9728, v9727, v9726, v9725, v110, v10194, v10193, v10192, v10182, v10191, v10183, v10190, v10185, v10184, v10189, v10188, v10187, v10186, v9795, v9794, v9793, v9783, v9792, v9784, v9791, v9786, v9785, v9790, v9789, v9788, v9787, ptr] using h3

theorem fetch_queue_head_no_prediction (s : State) (i : Inputs)
    (old : FetchQueueSequential s) : BitVec.extractLsb' 0 3 (v9795 s i) = 0 := by
  rcases fetch_queue_sequential_selected s i old with zero | ⟨eight, _⟩
  · rw [zero]
    rfl
  · rw [eight]
    rfl

theorem temporary_pc32_fetch_head_no_prediction_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) :
    BitVec.extractLsb' 0 3 (v9795 (run initial inputs (t + 1)) (inputs (t + 1))) = 0 :=
  fetch_queue_head_no_prediction _ _
    (temporary_pc32_fetch_queue_sequential_run initial inputs reset environment restriction t)

#print axioms fetch_queue_sequential_selected
#print axioms temporary_pc32_fetch_head_no_prediction_run
#print axioms temporary_pc32_fetch_queue_sequential_run
end NutShellProofs
