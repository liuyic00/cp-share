import Proofs.MulDivCheckedHolding
import Proofs.MulDivSignedCore

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

theorem correction_snapshot (s : State) (i later : Inputs)
    (correcting : s.r0_nstate = 5) (reset : i.nreset = 0) :
    (step s i).r16_ncontractWasNegated = 1 ∧
    v232 (step s i) later = BitVec.extractLsb' 0 64 s.r8_nremainder ∧
    v233 (step s i) later = BitVec.extractLsb' 65 64 s.r8_nremainder := by
  simp [step, eval_eq_spec, evalSpec, v232, v233, v176, v175, v174,
    v177, v178, v119, v144, v0, v1, v2, v31, v52, v53, reset, correcting]
  bv_decide

theorem snapshot_clear_on_capture (s : State) (i : Inputs) (capture : v2 s i = 1) :
    (step s i).r16_ncontractWasNegated = 0 := by
  simp only [step, eval_eq_spec, evalSpec, v176, v174, v31, v8, capture]
  bv_decide

theorem snapshot_hold (s : State) (i later : Inputs)
    (saved : s.r16_ncontractWasNegated = 1) (reset : i.nreset = 0)
    (noCapture : v2 s i = 0) (noCorrection : v53 s i = 0) :
    (step s i).r16_ncontractWasNegated = 1 ∧
    v232 (step s i) later = v232 s i ∧ v233 (step s i) later = v233 s i := by
  simp [step, eval_eq_spec, evalSpec, v232, v233, v176, v175, v174,
    v177, v178, v31, reset, saved, noCapture, noCorrection]

theorem unsaved_magnitudes (s : State) (i : Inputs) (unsaved : s.r16_ncontractWasNegated = 0) :
    v232 s i = BitVec.extractLsb' 0 64 s.r8_nremainder ∧
    v233 s i = BitVec.extractLsb' 65 64 s.r8_nremainder := by
  simp [v232, v233, v119, v144, unsaved]

theorem unsaved_before_correction (s : State) (i : Inputs)
    (unsaved : s.r16_ncontractWasNegated = 0)
    (notCorrecting : s.r0_nstate ≠ 5) :
    (step s i).r16_ncontractWasNegated = 0 := by
  simp [step, eval_eq_spec, evalSpec, v176, v175, v174, v53, v52,
    v31, v8, unsaved]
  bv_decide

theorem unsaved_run (s : State) (inputs : Nat → Inputs) (n : Nat)
    (unsaved : s.r16_ncontractWasNegated = 0)
    (notCorrecting : ∀ t, t < n → (run s inputs t).r0_nstate ≠ 5) :
    (run s inputs n).r16_ncontractWasNegated = 0 := by
  induction n with
  | zero => exact unsaved
  | succ n ih =>
    exact unsaved_before_correction (run s inputs n) (inputs n)
      (ih (by intro t h; exact notCorrecting t (by omega)))
      (notCorrecting n (by omega))

/-- Sign correction changes the datapath but preserves its original quotient
    and residue in the monitor, including the path with no correction edge. -/
theorem corrected_monitor_response (s : State) (i later : Inputs) (negative : BitVec 1)
    (finished : s.r0_nstate = HierarchicalMulDiv.finishState negative)
    (unsaved : s.r16_ncontractWasNegated = 0)
    (reset : i.nreset = 0) (alive : i.nio_5Fkill = 0) :
    let result := if negative = 1 then step s i else s
    v38 result later = 1 ∧
    v232 result later = BitVec.extractLsb' 0 64 s.r8_nremainder ∧
    v233 result later = BitVec.extractLsb' 65 64 s.r8_nremainder := by
  have response := HierarchicalMulDiv.corrected_response (coreState s)
    (coreInputs i) (coreInputs later) negative finished reset alive
  have projected : coreState (if negative = 1 then step s i else s) =
      (if negative = 1 then Core.step (coreState s) (coreInputs i) else coreState s) := by
    split <;> simp only [core_step]
  have valid : v38 (if negative = 1 then step s i else s) later = 1 := by
    have observed := core_observe (if negative = 1 then step s i else s) later
    rw [projected] at observed
    have h := congrArg (fun o => o.nio_5Fresp_5Fvalid) observed
    exact h.trans response.1
  refine ⟨valid, ?_⟩
  by_cases neg : negative = 1
  · have correcting : s.r0_nstate = 5 := by
      simpa [HierarchicalMulDiv.finishState, neg] using finished
    simpa only [neg, if_true] using (correction_snapshot s i later correcting reset).2
  · simpa only [neg, if_false] using unsaved_magnitudes s later unsaved

/-- Completed requests retain both monitor magnitudes while the response waits. -/
theorem terminal_magnitudes (s : State) (i later : Inputs)
    (valid : v38 s i = 1) (reset : i.nreset = 0) :
    v232 (step s i) later = v232 s i ∧
    v233 (step s i) later = v233 s i := by
  have terminal : s.r0_nstate = 6 ∨ s.r0_nstate = 7 := by
    simp only [v38, v36, v37, v35, v4] at valid
    bv_decide
  have bits := (terminal_payload s i valid).1
  change v151 s i = s.r8_nremainder at bits
  rcases terminal with done | done <;>
    simp [v232, v233, v119, v144, bits, step, eval_eq_spec, evalSpec,
      v176, v175, v174, v177, v178, v31, v0, v1, v2, v52, v53, done, reset]
  all_goals bv_decide

theorem division_monitor_format (s : State) (i : Inputs) (division : v198 s i = 1) :
    v258 s i = HierarchicalMulDiv.formatCorrected (v232 s i) (v233 s i)
      s.r12_ncontractDw (v221 s i) (v225 s i) := by
  simp only [v258, v257, v256, v255, v254, v253, division, if_true,
    v236, v235, v234, v143, HierarchicalMulDiv.formatCorrected]
  bv_decide

end HierarchicalMulDivChecked
