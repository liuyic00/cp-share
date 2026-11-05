import Proofs.ActiveFetchSuccessor
namespace NutShellProofs
open nNutCore

theorem fetch_enqueue_controls (s : State) (i : Inputs) (enqueue : v10241 s i = 1) :
    s.g51.r1643_nio_5Fimem_5Fcache_5Fstate = 5 ∧ v2697 s i = 1 ∧
    v9705 s i = 1 := by
  have ready : v2697 s i = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v2697 s i) with zero | one
    · simp [v10241, zero] at enqueue
    · exact one
  have response : v9705 s i = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v9705 s i) with zero | one
    · simp [v10241, v10240, v10239, v10238, v9709, v9708, v9707, v9706, zero] at enqueue
    · exact one
  have state : s.g51.r1643_nio_5Fimem_5Fcache_5Fstate = 5 := by
    by_cases state : s.g51.r1643_nio_5Fimem_5Fcache_5Fstate = BitVec.ofNat 3 5
    · exact state
    · simp [v9705, v9704, v9702, v9701, state] at response
  exact ⟨state, ready, response⟩

/-- An enqueued response releases the blocking fetch request immediately. -/
theorem fetch_enqueue_returns_idle (s : State) (i : Inputs) (enqueue : v10241 s i = 1) :
    (step s i).g51.r1643_nio_5Fimem_5Fcache_5Fstate = 0 := by
  obtain ⟨state, ready, response⟩ := fetch_enqueue_controls s i enqueue
  have transfer : v25873 s i = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v9698 s i) with zero | one
    all_goals simp_all [v25873, v25872, v25871, v25870, v25869, v9700, v9699, v2698]
  change v25883 s i = 0
  rcases BitVec.eq_zero_or_eq_one s.g51.r1645_nio_5Fimem_5Fcache_5FneedFlush with zero | one <;>
    rcases BitVec.eq_zero_or_eq_one s.g51.r1646_nio_5Fimem_5Fcache_5FalreadyOutFire with zero | one
  all_goals simp_all [v25883, v25882, v25804, v2687, v25881, v25840, v11531,
    v25880, v25846, v12711, v25879, v25851, v11537, v25878, v25860,
    v4, v25877, v25868, v9701, v25876, v25875, v25874]

theorem fetch_enqueue_excludes_capture (s : State) (i : Inputs) (enqueue : v10241 s i = 1) :
    v25943 s i = 0 := by
  have busy := fetch_enqueue_requires_active_response s i enqueue
  have busyLiteral : s.g51.r1643_nio_5Fimem_5Fcache_5Fstate ≠ BitVec.ofNat 3 0 := busy
  simp [v25943, v2689, v2688, v2687, busyLiteral]

#print axioms fetch_enqueue_returns_idle
#print axioms fetch_enqueue_excludes_capture

theorem temporary_pc32_enqueued_pc_successor (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (enqueue : v10241 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    v10265 (run initial inputs (t + 1)) (inputs (t + 1)) + 4 =
      (run initial inputs (t + 1)).g33.r1065_nfrontend_5Fifu_5Fpc := by
  have sequential := temporary_pc32_fetch_enqueue_metadata_run initial inputs reset
    environment restriction t enqueue
  exact sequential.1.symm.trans (fetch_enqueue_successor_is_ifu_pc _ _
    (active_fetch_successor_run initial inputs reset t) enqueue)

#print axioms temporary_pc32_enqueued_pc_successor
end NutShellProofs
