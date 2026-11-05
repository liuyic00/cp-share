import Proofs.TemporaryFrontendInvariant
namespace NutShellProofs
open nNutCore

/-- The cache metadata capture and IFU sequential advance share one handshake. -/
theorem fetch_capture_eq_advance (s : State) (i : Inputs) :
    v25943 s i = v9672 s i := rfl

theorem accepted_fetch_has_no_prediction (s : State) (i next : Inputs)
    (capture : v25943 (step s i) next = 1) :
    v2736 (step s i) next = 0 ∧ v2739 (step s i) next = 0 := by
  have advance : v9672 (step s i) next = 1 := capture
  constructor
  · rcases BitVec.eq_zero_or_eq_one (v2736 (step s i) next) with zero | one
    · exact zero
    · have stopped := prediction_excludes_fetch_advance s i next (Or.inl one)
      rw [stopped] at advance
      contradiction
  · rcases BitVec.eq_zero_or_eq_one (v2739 (step s i) next) with zero | one
    · exact zero
    · have stopped := prediction_excludes_fetch_advance s i next (Or.inr one)
      rw [stopped] at advance
      contradiction

/-- Exact request successor, not just its alignment. -/
theorem temporary_pc32_accepted_fetch_target (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (capture : v25943 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (noRedirect : v14 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    v2759 (run initial inputs (t + 1)) (inputs (t + 1)) =
      (run initial inputs (t + 1)).g33.r1065_nfrontend_5Fifu_5Fpc + 4 := by
  have prediction := accepted_fetch_has_no_prediction (run initial inputs t)
    (inputs t) (inputs (t + 1)) capture
  change v2736 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 ∧
    v2739 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 at prediction
  have clear := crossline_latch_clear_run initial inputs reset t
  have aligned := (temporary_pc32_frontend_pipeline_run initial inputs reset environment restriction t).fetch
  have bit1 := word_alignment_bit1 _ aligned
  simp [v2759, noRedirect, v2758, clear, v2757, prediction.1,
    frontend_sequential_address, bit1]

/-- Without a prediction or crossing latch, metadata records a sequential fetch. -/
theorem sequential_fetch_metadata_flags (s : State) (i : Inputs)
    (noRedirect : v14 s i = 0) (noPrediction : v2736 s i = 0)
    (noCrossPrediction : v2739 s i = 0)
    (clear : s.g33.r1066_nfrontend_5Fifu_5FcrosslineJumpLatch = 0) :
    v25957 s i = 8 := by
  have cross : v2738 s i = 0 := noCrossPrediction
  have mask : v25953 s i = 0 := by
    have shape : v25952 s i = ((1 : BitVec 1) ++ (0 : BitVec 3)) := by
      unfold v25952 v25950 v25951 v110 v4079
      rw [cross, noPrediction]
      rfl
    rw [v25953, shape]
    change ((0 : BitVec 1) ++ v2723 s i) &&& ((1 : BitVec 1) ++ (0 : BitVec 3)) = 0
    rw [BitVec.and_append]
    simp
  have high : v25947 s i = 1 := by
    simp [v25947, noRedirect, v25946, clear, v25945, noCrossPrediction,
      v25944, noPrediction, v110]
  have low : v25956 s i = 0 := by
    simp [v25956, noRedirect, v25955, v25954, mask]
  rw [v25957, high, low]
  rfl

theorem temporary_pc32_accepted_fetch_metadata (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (capture : v25943 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (noRedirect : v14 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    v25965 (run initial inputs (t + 1)) (inputs (t + 1)) =
      (0 : BitVec 5) ++ (((8 : BitVec 4) ++
        ((run initial inputs (t + 1)).g33.r1065_nfrontend_5Fifu_5Fpc + 4)) ++
        (run initial inputs (t + 1)).g33.r1065_nfrontend_5Fifu_5Fpc) := by
  have prediction := accepted_fetch_has_no_prediction (run initial inputs t)
    (inputs t) (inputs (t + 1)) capture
  change v2736 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 ∧
    v2739 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 at prediction
  have flags := sequential_fetch_metadata_flags _ _ noRedirect prediction.1 prediction.2
    (crossline_latch_clear_run initial inputs reset t)
  have target := temporary_pc32_accepted_fetch_target initial inputs reset environment restriction t capture noRedirect
  unfold v25965 v25964 v25963 v25962 v25961 v25960 v25959 v25958
  rw [flags, target]
  rfl

#print axioms temporary_pc32_accepted_fetch_metadata
#print axioms accepted_fetch_has_no_prediction
#print axioms temporary_pc32_accepted_fetch_target
#print axioms sequential_fetch_metadata_flags
end NutShellProofs
