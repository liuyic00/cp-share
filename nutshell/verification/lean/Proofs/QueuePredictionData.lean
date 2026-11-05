import Proofs.QueueSlotData
namespace NutShellProofs
open nNutCore

theorem queue_slot_prediction_pair_step_0 (s : State) (i : Inputs) (reset : i.g0.nreset = 0) :
    ((step s i).g52.r1681_ndataBuffer_5F0_5Fcf_5Fpnpc, (step s i).g52.r1680_ndataBuffer_5F0_5Fcf_5Fpc) =
      if v26198 s i = 1 ∧ (0 : BitVec 2) = s.g59.r1899_nringBufferHead then
        (s.g38.r1244_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpnpc, s.g38.r1243_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpc) else (s.g52.r1681_ndataBuffer_5F0_5Fcf_5Fpnpc, s.g52.r1680_ndataBuffer_5F0_5Fcf_5Fpc) := by
  change (v26275 s i, v26254 s i) = _
  by_cases enqueue : v26198 s i = 1
  · have valid := (queue_enqueue_single s i enqueue).1
    simp [v26262, v26263, v26264, v26265, v26266, v26267, v26268, v26269, v26270, v26271, v26273, v26274, v26275, v24, v9721, v26190, v26191, v26192, v26193, v26199, v26200, v26201, v26202, v26214, v26215, v26217, v26218, v26219, v26220, v26275, v26241, v26242, v26243, v26244, v26245, v26246, v26247, v26248, v26249, v26250, v26252, v26253, v26254, reset, enqueue, valid,
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 2 ≤ 2)] <;> split <;> simp_all
  · have idle : v26198 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right enqueue
    simp [v26274, v26275, v26275, v26253, v26254, reset, idle]

theorem queue_slot_prediction_pair_step_1 (s : State) (i : Inputs) (reset : i.g0.nreset = 0) :
    ((step s i).g54.r1736_ndataBuffer_5F1_5Fcf_5Fpnpc, (step s i).g54.r1735_ndataBuffer_5F1_5Fcf_5Fpc) =
      if v26198 s i = 1 ∧ (1 : BitVec 2) = s.g59.r1899_nringBufferHead then
        (s.g38.r1244_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpnpc, s.g38.r1243_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpc) else (s.g54.r1736_ndataBuffer_5F1_5Fcf_5Fpnpc, s.g54.r1735_ndataBuffer_5F1_5Fcf_5Fpc) := by
  change (v29267 s i, v29257 s i) = _
  by_cases enqueue : v26198 s i = 1
  · have valid := (queue_enqueue_single s i enqueue).1
    simp [v26264, v26265, v26266, v26267, v26268, v26269, v29260, v29261, v29262, v29263, v29265, v29266, v29267, v24, v9721, v26190, v26191, v26192, v26193, v26199, v26200, v26201, v26202, v26214, v26215, v26217, v26218, v26219, v26220, v26243, v26244, v26245, v26246, v26247, v26248, v29267, v29250, v29251, v29252, v29253, v29255, v29256, v29257, reset, enqueue, valid,
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 2 ≤ 2)] <;> split <;> simp_all
  · have idle : v26198 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right enqueue
    simp [v29266, v29267, v29267, v29256, v29257, reset, idle]

theorem queue_slot_prediction_pair_step_2 (s : State) (i : Inputs) (reset : i.g0.nreset = 0) :
    ((step s i).g55.r1791_ndataBuffer_5F2_5Fcf_5Fpnpc, (step s i).g55.r1790_ndataBuffer_5F2_5Fcf_5Fpc) =
      if v26198 s i = 1 ∧ (2 : BitVec 2) = s.g59.r1899_nringBufferHead then
        (s.g38.r1244_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpnpc, s.g38.r1243_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpc) else (s.g55.r1791_ndataBuffer_5F2_5Fcf_5Fpnpc, s.g55.r1790_ndataBuffer_5F2_5Fcf_5Fpc) := by
  change (v29811 s i, v29803 s i) = _
  by_cases enqueue : v26198 s i = 1
  · have valid := (queue_enqueue_single s i enqueue).1
    simp [v26264, v26265, v26266, v26267, v26268, v26269, v29805, v29806, v29807, v29809, v29810, v29811, v24, v9721, v26190, v26191, v26192, v26193, v26199, v26200, v26201, v26202, v26214, v26215, v26217, v26218, v26219, v26220, v26243, v26244, v26245, v26246, v26247, v26248, v29811, v29797, v29798, v29799, v29801, v29802, v29803, reset, enqueue, valid,
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 2 ≤ 2)] <;> split <;> simp_all
  · have idle : v26198 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right enqueue
    simp [v29810, v29811, v29811, v29802, v29803, reset, idle]

theorem queue_slot_prediction_pair_step_3 (s : State) (i : Inputs) (reset : i.g0.nreset = 0) :
    ((step s i).g57.r1846_ndataBuffer_5F3_5Fcf_5Fpnpc, (step s i).g57.r1845_ndataBuffer_5F3_5Fcf_5Fpc) =
      if v26198 s i = 1 ∧ (3 : BitVec 2) = s.g59.r1899_nringBufferHead then
        (s.g38.r1244_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpnpc, s.g38.r1243_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpc) else (s.g57.r1846_ndataBuffer_5F3_5Fcf_5Fpnpc, s.g57.r1845_ndataBuffer_5F3_5Fcf_5Fpc) := by
  change (v30251 s i, v30243 s i) = _
  by_cases enqueue : v26198 s i = 1
  · have valid := (queue_enqueue_single s i enqueue).1
    simp [v26264, v26265, v26266, v26267, v26268, v26269, v30245, v30246, v30247, v30249, v30250, v30251, v24, v2750, v9721, v26190, v26191, v26192, v26193, v26199, v26200, v26201, v26202, v26214, v26215, v26217, v26218, v26219, v26220, v26243, v26244, v26245, v26246, v26247, v26248, v30251, v30237, v30238, v30239, v30241, v30242, v30243, reset, enqueue, valid,
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 2 ≤ 2)] <;> split <;> simp_all
  · have idle : v26198 s i = 0 := (BitVec.eq_zero_or_eq_one _).resolve_right enqueue
    simp [v30250, v30251, v30251, v30242, v30243, reset, idle]


def QueuePredictionPair (s : State) (slot : BitVec 2) : BitVec 39 × BitVec 39 :=
  if slot = 0 then (s.g52.r1681_ndataBuffer_5F0_5Fcf_5Fpnpc, s.g52.r1680_ndataBuffer_5F0_5Fcf_5Fpc) else
  if slot = 1 then (s.g54.r1736_ndataBuffer_5F1_5Fcf_5Fpnpc, s.g54.r1735_ndataBuffer_5F1_5Fcf_5Fpc) else
  if slot = 2 then (s.g55.r1791_ndataBuffer_5F2_5Fcf_5Fpnpc, s.g55.r1790_ndataBuffer_5F2_5Fcf_5Fpc) else
  (s.g57.r1846_ndataBuffer_5F3_5Fcf_5Fpnpc, s.g57.r1845_ndataBuffer_5F3_5Fcf_5Fpc)

theorem queue_prediction_pair_step (s : State) (i : Inputs) (slot : BitVec 2)
    (reset : i.g0.nreset = 0) :
    QueuePredictionPair (step s i) slot =
      if v26198 s i = 1 ∧ slot = s.g59.r1899_nringBufferHead then
        (s.g38.r1244_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpnpc,
          s.g38.r1243_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5Fpc)
      else QueuePredictionPair s slot := by
  have bound := slot.isLt
  have cases : slot.toNat = 0 ∨ slot.toNat = 1 ∨ slot.toNat = 2 ∨ slot.toNat = 3 := by omega
  rcases cases with c | c | c | c
  · have eq : slot = (0 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [QueuePredictionPair, eq] using queue_slot_prediction_pair_step_0 s i reset
  · have eq : slot = (1 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [QueuePredictionPair, eq] using queue_slot_prediction_pair_step_1 s i reset
  · have eq : slot = (2 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [QueuePredictionPair, eq] using queue_slot_prediction_pair_step_2 s i reset
  · have eq : slot = (3 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simpa [QueuePredictionPair, eq] using queue_slot_prediction_pair_step_3 s i reset

theorem queue_selected_prediction_pair (s : State) (i : Inputs) :
    (v24327 s i, v24312 s i) = QueuePredictionPair s s.g59.r1900_nringBufferTail := by
  have bound := s.g59.r1900_nringBufferTail.isLt
  have cases : s.g59.r1900_nringBufferTail.toNat = 0 ∨
      s.g59.r1900_nringBufferTail.toNat = 1 ∨
      s.g59.r1900_nringBufferTail.toNat = 2 ∨
      s.g59.r1900_nringBufferTail.toNat = 3 := by omega
  rcases cases with c | c | c | c
  · have eq : s.g59.r1900_nringBufferTail = (0 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simp [v24314, v24315, v24316, v24317, v24318, v24319, v24320, v24321, v24322, v24323, v24324, v24325, v24326, v24327, QueuePredictionPair, v24327, v24299, v24300, v24301, v24302, v24303, v24304, v24305, v24306, v24307, v24308, v24309, v24310, v24311, v24312, v2750, v9721, v110, eq]
  · have eq : s.g59.r1900_nringBufferTail = (1 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simp [v24314, v24315, v24316, v24317, v24322, v24323, v24324, v24325, v24326, v24327, QueuePredictionPair, v24327, v24299, v24300, v24301, v24302, v24307, v24308, v24309, v24310, v24311, v24312, v2750, v9721, eq]
  · have eq : s.g59.r1900_nringBufferTail = (2 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simp [v24314, v24315, v24323, v24324, v24325, v24326, v24327, QueuePredictionPair, v24327, v24299, v24300, v24308, v24309, v24310, v24311, v24312, v2750, v9721, eq]
  · have eq : s.g59.r1900_nringBufferTail = (3 : BitVec 2) := BitVec.eq_of_toNat_eq (by simpa using c)
    simp [v24314, v24324, v24325, v24326, v24327, QueuePredictionPair, v24327, v24299, v24309, v24310, v24311, v24312, v2750, eq]

#print axioms queue_prediction_pair_step
#print axioms queue_selected_prediction_pair
end NutShellProofs
