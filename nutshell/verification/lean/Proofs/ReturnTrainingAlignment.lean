import Proofs.ReturnPredictionAlignment
namespace NutShellProofs
open nNutCore

/-- ALU training captures the execute PC and instruction width together. -/
theorem return_training_capture (s : State) (i : Inputs)
    (pc : BitVec.extractLsb' 0 2 s.g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc = 0)
    (width : BitVec.extractLsb' 0 2 (v11547 s i) = 3) (next : Inputs) :
    BitVec.extractLsb' 0 2 (v73 (step s i) next) = 0 ∧
    v104 (step s i) next = 0 := by
  constructor
  · change BitVec.extractLsb' 0 2 (v12145 s i) = 0
    exact pc
  · change v12193 s i = 0
    simp [v12193, v12192, v12191, width, v2750]

/-- The actual training-valid signal requires a valid ALU execute input. -/
theorem return_training_requires_execute (s : State) (i next : Inputs)
    (training : v63 (step s i) next = 1) : v6 s i = 1 := by
  change v12143 s i = 1 at training
  rcases BitVec.eq_zero_or_eq_one (v6 s i) with zero | one
  · simp [v12143, v12140, v12139, v12137, zero] at training
  · exact one

/-- Training valid is not reset-gated: these execute values still train even
when the input reset is asserted. This is a local transition fact, not a
reachable counterexample to the original assertions. -/
theorem return_training_valid_without_reset_gate (s : State) (i next : Inputs)
    (valid : v6 s i = 1) (unit : v3 s i = 0)
    (flush : v23 s i = 0) (operation : v28 s i = 92) :
    v63 (step s i) next = 1 := by
  change v12143 s i = 1
  simp [v12143, v12140, v12139, v12137, v12136, v12135,
    v12138, v24, v12142, v12141, valid, unit, flush, operation]

/-- Conditional induction for the real stack and its valid prediction target.
Training alignment is still a reachable-pipeline obligation, not Environment. -/
theorem return_stack_and_prediction_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (training : ∀ k, v63 (run initial inputs (k + 1)) (inputs (k + 1)) = 1 →
      v8208 (run initial inputs (k + 1)) (inputs (k + 1)) = 1 →
      BitVec.extractLsb' 0 2 (v73 (run initial inputs (k + 1)) (inputs (k + 1))) = 0 ∧
      v104 (run initial inputs (k + 1)) (inputs (k + 1)) = 0)
    (t : Nat) : ReturnStackAligned (run initial inputs (t + 1)) ∧
      ReturnPredictionAligned (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact ⟨return_stack_reset _ _ reset, return_prediction_reset _ _ reset⟩
  | succ t ih =>
    constructor
    · apply return_stack_step _ _ ih.1
      intro valid call
      obtain ⟨pc, width⟩ := training t valid call
      exact return_stack_push_aligned _ _ pc width
    · exact return_prediction_step _ _ ih.1

#print axioms return_training_valid_without_reset_gate
#print axioms return_training_capture
#print axioms return_training_requires_execute
#print axioms return_stack_and_prediction_run
end NutShellProofs
