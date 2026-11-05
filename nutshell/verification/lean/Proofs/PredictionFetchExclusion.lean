import Proofs.ReturnPredictionAlignment
namespace NutShellProofs
open nNutCore

/-- A live prediction follows an accepted, non-flushed fetch, whose cache is
busy in the prediction cycle. This does not require target alignment. -/
theorem prediction_requires_busy_fetch (s : State) (i next : Inputs)
    (enabled : v2736 (step s i) next = 1 ∨ v2739 (step s i) next = 1) :
    (step s i).g51.r1643_nio_5Fimem_5Fcache_5Fstate ≠ 0 := by
  have hit := prediction_enabled_lookup_hit (step s i) next enabled
  change v4063 s i = 1 at hit
  have reset : i.g0.nreset ≠ BitVec.ofNat 1 1 := by
    intro r
    simp [v4063, v2, v1, v0, r, v24] at hit
  have capture : v2701 s i = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v2701 s i) with zero | one
    · simp [v4063, v4062, v2702, zero, v24] at hit
    · exact one
  have noRedirect : v14 s i ≠ BitVec.ofNat 1 1 := by
    intro redirect
    have flushed : (step s i).g16.r517_nfrontend_5Fifu_5Fbp1_5Fflush = 1 := by
      change v4050 s i = 1
      simp [v4050, v2, v1, v0, reset, v4049, v4047, redirect, v110]
    simp [v2736, v2735, v2739, v2738, v2727, v2720,
      v2719, v2718, flushed, v24] at enabled
  have idle : s.g51.r1643_nio_5Fimem_5Fcache_5Fstate = 0 := by
    by_cases busy : s.g51.r1643_nio_5Fimem_5Fcache_5Fstate = BitVec.ofNat 3 0
    · exact busy
    · simp [v2701, v2700, v2693, v2692, v2691, v2690, v2689, v2688,
        v2687, busy] at capture
  have ready : v2699 s i = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v2699 s i) with zero | one
    · simp [v2701, v2700, zero] at capture
    · exact one
  change v25883 s i ≠ 0
  by_cases mmio : v25837 s i = BitVec.ofNat 1 1
  all_goals simp [mmio, v25883, v25803, reset, v25882, v25804, v2687, idle,
    v25839, v25818, v25809, v2689, v2688, v25808, v25807, v25806,
    v25805, ready, v25817, v25816, v25815, v25814, v25813, v25812,
    v25811, v25810, v19, v18, v17, noRedirect, v16, v24, v4079,
    v25838, v11537, v11531]

/-- A live prediction cannot coincide with the sequential fetch advance. -/
theorem prediction_excludes_fetch_advance (s : State) (i next : Inputs)
    (enabled : v2736 (step s i) next = 1 ∨ v2739 (step s i) next = 1) :
    v9672 (step s i) next = 0 := by
  have busy := prediction_requires_busy_fetch s i next enabled
  have busy' : (step s i).g51.r1643_nio_5Fimem_5Fcache_5Fstate ≠ BitVec.ofNat 3 0 := busy
  simp [v9672, v2693, v2692, v2691, v2690, v2689, v2688, v2687, busy']

/-- Whenever a live prediction coincides with an IFU update, the redirect mux
has priority over that prediction. -/
theorem prediction_update_requires_redirect (s : State) (i next : Inputs)
    (enabled : v2736 (step s i) next = 1 ∨ v2739 (step s i) next = 1)
    (update : v9673 (step s i) next = 1) : v14 (step s i) next = 1 := by
  have stopped := prediction_excludes_fetch_advance s i next enabled
  simpa [v9673, stopped] using update

theorem crossline_latch_stays_clear (s : State) (i : Inputs)
    (clear : s.g33.r1066_nfrontend_5Fifu_5FcrosslineJumpLatch = 0)
    (excluded : v2739 s i = 1 → v9672 s i = 0) :
    (step s i).g33.r1066_nfrontend_5Fifu_5FcrosslineJumpLatch = 0 := by
  change v9681 s i = 0
  by_cases redirect : v14 s i = BitVec.ofNat 1 1
  · simp [v9681, v9680, v9679, v9676, v9673, v4047, redirect, clear, v24]
  · rcases BitVec.eq_zero_or_eq_one (v2739 s i) with zero | one
    · simp [v9681, v9680, v9679, v9678, zero, clear, v24]
    · have stopped := excluded one
      simp [v9681, v9680, v9676, v9673, v4047, stopped, clear, v24,
        redirect]

theorem crossline_latch_clear_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    (run initial inputs (t + 1)).g33.r1066_nfrontend_5Fifu_5FcrosslineJumpLatch = 0 := by
  induction t with
  | zero =>
    change v9681 initial (inputs 0) = 0
    simp [v9681, v1, v0, reset, v24]
  | succ t ih =>
    apply crossline_latch_stays_clear _ _ ih
    intro enabled
    exact prediction_excludes_fetch_advance (run initial inputs t) (inputs t)
      (inputs (t + 1)) (Or.inr enabled)

#print axioms crossline_latch_clear_run
#print axioms crossline_latch_stays_clear
#print axioms prediction_excludes_fetch_advance
#print axioms prediction_update_requires_redirect
#print axioms prediction_requires_busy_fetch
end NutShellProofs
