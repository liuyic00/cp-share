import Proofs.FetchQueueSequential
namespace NutShellProofs
open nNutCore

theorem aligned_offset_zero_or_four (offset : BitVec 3)
    (aligned : BitVec.extractLsb' 0 2 offset = 0) : offset = 0 ∨ offset = 4 := by
  have bound := offset.isLt
  have low := congrArg BitVec.toNat aligned
  simp [BitVec.extractLsb'_toNat] at low
  have cases : offset.toNat = 0 ∨ offset.toNat = 4 := by omega
  rcases cases with zero | four
  · left
    exact BitVec.eq_of_toNat_eq (by simpa using zero)
  · right
    exact BitVec.eq_of_toNat_eq (by simpa using four)

/-- A full-width word at an aligned offset consumes the current fetch entry. -/
theorem frontend_word_consumption_controls (s : State) (i : Inputs)
    (aligned : BitVec.extractLsb' 0 2 (v9735 s i) = 0)
    (full : v9780 s i = 0) : v10067 s i = 1 ∧ v10087 s i = 0 := by
  rcases aligned_offset_zero_or_four (v9735 s i) aligned with zero | four
  all_goals rcases BitVec.eq_zero_or_eq_one (BitVec.extractLsb' 0 1 (v9795 s i)) with bitZero | bitOne
  all_goals simp_all [v10067, v10064, v10058, v10052, v10048, v10047,
    v10051, v10049, v10050, v10057, v10053, v4, v10056, v10054, v10055,
    v10063, v10060, v10059, v10062, v10066, v10065, v97, v24,
    v10087, v10079, v10073, v10072, v10078, v10077, v10086,
    v10083, v10081, v10080]

theorem frontend_word_state_step (s : State) (i : Inputs)
    (state : s.g33.r1072_nfrontend_5Fibf_5Fstate = 0)
    (head : BitVec.extractLsb' 0 2 (v9733 s i) = 0)
    (environment : assumes s i) :
    (step s i).g33.r1072_nfrontend_5Fibf_5Fstate = 0 := by
  rcases BitVec.eq_zero_or_eq_one i.g0.nreset with noReset | reset
  · have aligned : BitVec.extractLsb' 0 2 (v9735 s i) = 0 := by
      simpa [v9735, v9719, v9718, v4079, state, v9734,
        low_low _ (by decide : 2 ≤ 3)] using head
    have crossing := frontend_aligned_crossing_signals_zero s i aligned
    have noPartial : v10102 s i = 0 := by
      rcases BitVec.eq_zero_or_eq_one (v10100 s i) with empty | valid
      · simp [v10102, v10101, empty]
      · have full := original_assumptions_disable_compressed_output s i environment noReset valid
        have control := (frontend_word_consumption_controls s i aligned full).2
        simp [v10102, control]
    change v10128 s i = 0
    simp [v10128, v10127, v10126, v9718, v4079, state,
      v10108, crossing.1, v10107, crossing.2.1, v10106, noPartial, v10105]
  · change v10128 s i = 0
    simp [v10128, v9714, v0, reset, v4079]

theorem temporary_pc32_frontend_word_state_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) :
    (run initial inputs (t + 1)).g33.r1072_nfrontend_5Fibf_5Fstate = 0 := by
  induction t with
  | zero =>
    change v10128 initial (inputs 0) = 0
    simp [v10128, v9714, v0, reset, v4079]
  | succ t ih =>
    exact frontend_word_state_step _ _ ih
      (fetch_queue_pc_selected _ _
        (temporary_pc32_frontend_pipeline_run initial inputs reset environment restriction t).queue)
      (environment (t + 1))

theorem frontend_word_output_pc (s : State) (i : Inputs)
    (state : s.g33.r1072_nfrontend_5Fibf_5Fstate = 0)
    (noRedirect : v14 s i = 0) : v10174 s i = v9733 s i := by
  simp [v10174, v10167, v9717, v9716, v9715, v18, v17, noRedirect,
    v16, v24, v110, v10173, v9718, v4079, state]

theorem temporary_pc32_frontend_output_pc_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (noRedirect : v14 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    v10174 (run initial inputs (t + 1)) (inputs (t + 1)) =
      v9733 (run initial inputs (t + 1)) (inputs (t + 1)) :=
  frontend_word_output_pc _ _
    (temporary_pc32_frontend_word_state_run initial inputs reset environment restriction t) noRedirect

#print axioms temporary_pc32_frontend_output_pc_run
#print axioms temporary_pc32_frontend_word_state_run
#print axioms aligned_offset_zero_or_four
#print axioms frontend_word_consumption_controls
end NutShellProofs
