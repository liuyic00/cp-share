import Proofs.FrontendWordConsumption
namespace NutShellProofs
open nNutCore

/-- Under the proved word-only frontend conditions, one dequeue is exactly one
IDU capture. In particular a stalled consumer cannot silently discard a word. -/
theorem frontend_word_dequeue_eq_capture (s : State) (i : Inputs)
    (state : s.g33.r1072_nfrontend_5Fibf_5Fstate = 0)
    (aligned : BitVec.extractLsb' 0 2 (v9735 s i) = 0)
    (reset : i.g0.nreset = 0) (noRedirect : v14 s i = 0)
    (environment : assumes s i) : v11083 s i = v11102 s i := by
  have noCrossing : v11079 s i = 0 := by
    have notSix : v9735 s i ≠ BitVec.ofNat 3 6 := by
      intro six
      rw [six] at aligned
      contradiction
    simp [v11079, v11077, v11076, v11075, v9809, v9806, v9804,
      v9797, v9782, v9736, v97, notSix]
  rcases BitVec.eq_zero_or_eq_one (v10100 s i) with empty | valid
  · rcases BitVec.eq_zero_or_eq_one (v9802 s i) with zero | one
    all_goals simp_all [v11083, v11082, v11081, v11080, v11071,
      v11051, v11070, v11052, v11102, v24, v9802]
  · have full := original_assumptions_disable_compressed_output s i environment reset valid
    have consume := (frontend_word_consumption_controls s i aligned full).1
    have queueValid : v9802 s i = 1 := by
      rcases BitVec.eq_zero_or_eq_one (v9802 s i) with zero | one
      · simp [v10100, v10099, zero] at valid
      · exact one
    have extra : v11063 s i = 0 := by
      rcases aligned_offset_zero_or_four (v9735 s i) aligned with zero | four
      all_goals simp_all [v11063, v11060, v11057, v11055, v11054]
    have queued : v9801 s i = 1 := queueValid
    rcases BitVec.eq_zero_or_eq_one (v10044 s i) with stalled | ready
    all_goals simp_all [v11083, v11082, v11081, v11080, v11071, v11051,
      v24, v11070, v11052, v11069, v11053, v9717,
      v9716, v9715, v18, v17, v16, v110, v11068, v9718,
      v4079, v11064, v11102, v10045]

theorem temporary_pc32_dequeue_eq_capture_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (currentReset : (inputs (t + 1)).g0.nreset = 0)
    (noRedirect : v14 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    v11083 (run initial inputs (t + 1)) (inputs (t + 1)) =
      v11102 (run initial inputs (t + 1)) (inputs (t + 1)) := by
  have invariant := temporary_pc32_frontend_pipeline_run initial inputs reset environment restriction t
  have head := fetch_queue_pc_selected _ (inputs (t + 1)) invariant.queue
  exact frontend_word_dequeue_eq_capture _ _
    (temporary_pc32_frontend_word_state_run initial inputs reset environment restriction t)
    (frontend_selected_offset_aligned _ _ head invariant.buffer.2)
    currentReset noRedirect (environment (t + 1))

theorem fetch_dequeue_pointer_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (noRedirect : v14 s i = 0)
    (handshake : v11083 s i = v11102 s i) :
    (step s i).g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue =
      if v11102 s i = 1 then s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue + 1
      else s.g38.r1239_nfrontend_5Fibf_5Fio_5Fin_5Fq_5Fdeq_5Fptr_5Fvalue := by
  change v11090 s i = _
  simp [v11090, v10235, v0, reset, v11089, v11041, v11040, v18, v17,
    noRedirect, v16, v11088, handshake, v11087, v11086, v11084, v11085,
    low_add _ _ (by decide : 2 ≤ 3),
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 2 ≤ 2)]

#print axioms temporary_pc32_dequeue_eq_capture_run
#print axioms fetch_dequeue_pointer_step
#print axioms frontend_word_dequeue_eq_capture
end NutShellProofs
