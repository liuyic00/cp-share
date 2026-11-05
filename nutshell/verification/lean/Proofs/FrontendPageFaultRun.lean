import Proofs.FrontendPageFaults
namespace NutShellProofs
open nNutCore

def FrontendPageFaultClear (s : State) : Prop :=
  FrontendPageFaultSlotsClear s ∧ s.g33.r1078_nfrontend_5Fibf_5FspecialIPFR = 0 ∧
    (s.g38.r1241_nfrontend_5Fvalid = 1 →
      s.g39.r1260_nfrontend_5Fidu_5Fio_5Fin_5F0_5Fbits_5Fr_5FexceptionVec_5F12 = 0)

theorem frontend_page_fault_clear_reset (s : State) (i : Inputs)
    (reset : i.g0.nreset = 1) : FrontendPageFaultClear (step s i) := by
  refine ⟨frontend_page_fault_slots_reset s i reset, ?_, ?_⟩
  · change v10220 s i = 0
    simp [v10220, v9714, v0, v24, reset]
  · intro valid
    change v11101 s i = 1 at valid
    simp [v11101, v0, v24, reset] at valid

theorem frontend_page_fault_clear_step (s : State) (i : Inputs)
    (old : FrontendPageFaultClear s) : FrontendPageFaultClear (step s i) := by
  obtain ⟨slots, special, idu⟩ := old
  have selected := frontend_selected_page_fault_zero s i slots
  have source : v11332 s i = 0 := by
    simp [v11332, v11331, v11330, selected, special]
  refine ⟨frontend_page_fault_slots_step s i slots, ?_, ?_⟩
  · change v10220 s i = 0
    simp [v10220, v10219, v10218, v10217, v10216, v10215, v10214,
      v10213, selected, special, v24]
  · intro valid
    change v11333 s i = 0
    by_cases fire : v11102 s i = 1
    · simp [v11333, fire, source]
    · rw [v11333, if_neg fire]
      apply idu
      have noCapture : v11096 s i ≠ 1 := fire
      change v11101 s i = 1 at valid
      unfold v11101 at valid
      split at valid
      · simp [v24] at valid
      · unfold v11100 at valid
        split at valid
        · simp [v24] at valid
        · simp only [v11099, noCapture, ↓reduceIte] at valid
          unfold v11098 at valid
          split at valid
          · simp [v24] at valid
          · exact valid

theorem frontend_page_fault_clear_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    FrontendPageFaultClear (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact frontend_page_fault_clear_reset initial (inputs 0) reset
  | succ t ih => exact frontend_page_fault_clear_step _ _ ih

theorem active_idu_page_fault_zero_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (valid : v9827 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    v26909 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := by
  exact (frontend_page_fault_clear_run initial inputs reset t).2.2 valid
#print axioms frontend_page_fault_clear_run
#print axioms active_idu_page_fault_zero_run
/-- For valid active-port decode, only interrupt/access-fault override sources remain. -/
theorem active_idu_override_sources_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (valid : v9827 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    v28261 (run initial inputs (t + 1)) (inputs (t + 1)) =
      (v10039 (run initial inputs (t + 1)) (inputs (t + 1)) |||
       v26367 (run initial inputs (t + 1)) (inputs (t + 1))) := by
  simp [v28261, v28260, active_idu_page_fault_zero_run initial inputs reset t valid]
#print axioms active_idu_override_sources_run
end NutShellProofs
