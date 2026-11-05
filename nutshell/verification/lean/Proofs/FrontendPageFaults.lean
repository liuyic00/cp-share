import Proofs.InactiveDecodePort
namespace NutShellProofs
open nNutCore
def FrontendPageFaultSlotsClear (s : State) : Prop :=
  s.g34.r1100_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F0_5FexceptionVec_5F12 = 0 ∧ s.g35.r1139_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F1_5FexceptionVec_5F12 = 0 ∧ s.g36.r1178_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F2_5FexceptionVec_5F12 = 0 ∧ s.g38.r1217_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fregs_5F3_5FexceptionVec_5F12 = 0
theorem frontend_page_fault_slots_reset (s : State) (i : Inputs)
    (reset : i.g0.nreset = 1) :
    FrontendPageFaultSlotsClear (step s i) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change v10391 s i = 0
    simp [v10391, v10235, v0, v24, v10390, v10389, v10388, v10387, v10386, v10385, v10384, reset]
  · change v10627 s i = 0
    simp [v10627, v10235, v0, v24, v10626, v10625, v10624, v10623, v10388, v10387, v10386, v10385, v10384, reset]
  · change v10803 s i = 0
    simp [v10803, v10235, v0, v24, v10802, v10801, v10800, v9721, v10388, v10387, v10386, v10385, v10384, reset]
  · change v10959 s i = 0
    simp [v10959, v10235, v0, v24, v10958, v10957, v10956, v2750, v10388, v10387, v10386, v10385, v10384, reset]
theorem frontend_page_fault_slots_step (s : State) (i : Inputs)
    (old : FrontendPageFaultSlotsClear s) :
    FrontendPageFaultSlotsClear (step s i) := by
  rcases old with ⟨h0,h1,h2,h3⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · change v10391 s i = 0
    simp [v10391, v10235, v0, v24, v10390, v10389, v10388, v10387, v10386, v10385, v10384, h0, h1, h2, h3]
  · change v10627 s i = 0
    simp [v10627, v10235, v0, v24, v10626, v10625, v10624, v10623, v10388, v10387, v10386, v10385, v10384, h0, h1, h2, h3]
  · change v10803 s i = 0
    simp [v10803, v10235, v0, v24, v10802, v10801, v10800, v9721, v10388, v10387, v10386, v10385, v10384, h0, h1, h2, h3]
  · change v10959 s i = 0
    simp [v10959, v10235, v0, v24, v10958, v10957, v10956, v2750, v10388, v10387, v10386, v10385, v10384, h0, h1, h2, h3]
theorem frontend_page_fault_slots_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    FrontendPageFaultSlotsClear (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact frontend_page_fault_slots_reset initial (inputs 0) reset
  | succ t ih => exact frontend_page_fault_slots_step _ _ ih
theorem frontend_selected_page_fault_zero (s : State) (i : Inputs)
    (slots : FrontendPageFaultSlotsClear s) : v10212 s i = 0 := by
  rcases slots with ⟨h0,h1,h2,h3⟩
  have bound := s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue.isLt
  have cases : s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = 0 ∨ s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = 1 ∨ s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = 2 ∨ s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue = 3 := by
    have n : ∀ x : BitVec 2, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by decide
    exact n _
  rcases cases with h | h | h | h <;>
    simp [v10212, v10211, v10210, v10200, v2750, v10209, v10201, v9721, v10208, v10203, v10202, v10207, v10206, v10205, v10204, v110, h, h0, h1, h2, h3]
#print axioms frontend_page_fault_slots_run
#print axioms frontend_selected_page_fault_zero
end NutShellProofs
