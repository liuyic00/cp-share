import Proofs.ReturnStackRead
namespace NutShellProofs
open nNutCore

/-- Constrain the unreset target only while the registered lookup is valid. -/
def ReturnPredictionAligned (s : State) : Prop :=
  s.g16.r520_nfrontend_5Fifu_5Fbp1_5FbtbHit_5FREG = 1 →
    BitVec.extractLsb' 0 2 s.g32.r1054_nfrontend_5Fifu_5Fbp1_5FrasTarget = 0

theorem return_prediction_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    ReturnPredictionAligned (step s i) := by
  intro hit
  change v4063 s i = 1 at hit
  simp [v4063, v2, v1, v0, v24, reset] at hit

/-- A valid next lookup captures the stack read in the same transition. -/
theorem return_prediction_step (s : State) (i : Inputs)
    (slots : ReturnStackAligned s) : ReturnPredictionAligned (step s i) := by
  intro hit
  have capture : v2701 s i = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v2701 s i) with zero | one
    · change v4063 s i = 1 at hit
      simp [v4063, v4062, v2702, zero, v24] at hit
    · exact one
  exact return_target_capture_aligned s i slots capture

theorem prediction_enabled_lookup_hit (s : State) (i : Inputs)
    (enabled : v2736 s i = 1 ∨ v2739 s i = 1) :
    s.g16.r520_nfrontend_5Fifu_5Fbp1_5FbtbHit_5FREG = 1 := by
  rcases BitVec.eq_zero_or_eq_one s.g16.r520_nfrontend_5Fifu_5Fbp1_5FbtbHit_5FREG with zero | one
  · simp [v2736, v2735, v2739, v2738, v2727, v2720, zero] at enabled
  · exact one

theorem enabled_return_prediction_aligned (s : State) (i : Inputs)
    (valid : ReturnPredictionAligned s)
    (enabled : v2736 s i = 1 ∨ v2739 s i = 1) :
    BitVec.extractLsb' 0 2 s.g32.r1054_nfrontend_5Fifu_5Fbp1_5FrasTarget = 0 :=
  valid (prediction_enabled_lookup_hit s i enabled)

/-- The non-return BTB target remains an explicit proof obligation. -/
theorem enabled_prediction_target_aligned (s : State) (i : Inputs)
    (valid : ReturnPredictionAligned s)
    (enabled : v2736 s i = 1 ∨ v2739 s i = 1)
    (btb : v2751 s i ≠ 1 → BitVec.extractLsb' 0 2 (v2753 s i) = 0) :
    BitVec.extractLsb' 0 2 (v2755 s i) = 0 := by
  unfold v2755 v2754
  split
  · exact enabled_return_prediction_aligned s i valid enabled
  · exact btb (by assumption)

/-- BTB initialization disables the next lookup, irrespective of RAS data. -/
theorem initializing_btb_disables_prediction (s : State) (i next : Inputs)
    (initializing : s.g16.r512_nfrontend_5Fifu_5Fbp1_5Fbtb_5F_5FresetState = 1) :
    v2736 (step s i) next ≠ 1 ∧ v2739 (step s i) next ≠ 1 := by
  have noHit : (step s i).g16.r520_nfrontend_5Fifu_5Fbp1_5FbtbHit_5FREG = 0 := by
    change v4063 s i = 0
    simp [v4063, v4062, v4061, v4060, v4058, initializing, v24]
  constructor
  · intro enabled
    have hit := prediction_enabled_lookup_hit (step s i) next (Or.inl enabled)
    simp [noHit] at hit
  · intro enabled
    have hit := prediction_enabled_lookup_hit (step s i) next (Or.inr enabled)
    simp [noHit] at hit

#print axioms initializing_btb_disables_prediction
#print axioms enabled_prediction_target_aligned
#print axioms return_prediction_reset
#print axioms return_prediction_step
#print axioms prediction_enabled_lookup_hit
#print axioms enabled_return_prediction_aligned
end NutShellProofs
