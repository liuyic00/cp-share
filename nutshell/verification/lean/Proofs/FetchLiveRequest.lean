import Proofs.FetchOutstanding
namespace NutShellProofs
open nNutCore

def LiveFetchRequest (s : State) : Prop :=
  s.g51.r1643_nio_5Fimem_5Fcache_5Fstate ≠ 0 ∧
  s.g51.r1645_nio_5Fimem_5Fcache_5FneedFlush = 0

theorem fetch_capture_requires_idle (s : State) (i : Inputs)
    (capture : v25943 s i = 1) : s.g51.r1643_nio_5Fimem_5Fcache_5Fstate = 0 := by
  by_cases idle : s.g51.r1643_nio_5Fimem_5Fcache_5Fstate = BitVec.ofNat 3 0
  · exact idle
  · simp [v25943, v2689, v2688, v2687, idle] at capture

theorem fetch_capture_becomes_live (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (redirect : v14 s i = 0)
    (capture : v25943 s i = 1) : LiveFetchRequest (step s i) := by
  have idle := fetch_capture_requires_idle s i capture
  have request : v25809 s i = 1 := capture
  have start : v25818 s i = 1 := by
    simp [v25818, request, v25817, v25816, v25815, v25814, v25813,
      v25812, v25811, v25810, v19, v18, v17, redirect, v16, v24, v4079]
  constructor
  · change v25883 s i ≠ 0
    by_cases mmio : v25837 s i = BitVec.ofNat 1 1
    all_goals simp [v25883, v25803, reset, v25882, v25804, idle, v2687,
      v25839, start, v25838, v11537, v11531, mmio]
  · change v25893 s i = 0
    rcases BitVec.eq_zero_or_eq_one s.g51.r1645_nio_5Fimem_5Fcache_5FneedFlush with zero | one
    all_goals simp_all [v25893, v25803, v25892, v25887, v25886,
      v2687, v25891, v25890, v25889, v24]

theorem fetch_reset_not_live (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    ¬ LiveFetchRequest (step s i) := by
  intro live
  have active := live.1
  change v25883 s i ≠ 0 at active
  simp [v25883, v25803, reset, v2687] at active

theorem fetch_redirect_not_live (s : State) (i : Inputs) (redirect : v14 s i = 1) :
    ¬ LiveFetchRequest (step s i) := by
  rcases BitVec.eq_zero_or_eq_one i.g0.nreset with noReset | reset
  · by_cases idle : s.g51.r1643_nio_5Fimem_5Fcache_5Fstate = BitVec.ofNat 3 0
    · intro live
      have active := live.1
      change v25883 s i ≠ 0 at active
      simp [v25883, v25882, v25804, idle, v2687, v25839,
        v25818, v25817, v25816, v25815, v25814, v25813, v25812,
        v25811, v25810, v19, v18, v17, redirect, v15, v2750, v24] at active
    · intro live
      have clear : v25893 s i = 0 := live.2
      simp [v25893, v25803, noReset, v25892, v25887, v25886, v2687,
        idle, v25891, v25890, v25889, v25888, v25815, v25814,
        v25813, v25812, v25811, v25810, v19, v18, v17, redirect, v15,
        v24, v2750, v110] at clear
  · exact fetch_reset_not_live s i reset

#print axioms fetch_capture_becomes_live
#print axioms fetch_redirect_not_live

theorem fetch_busy_flush_flag_hold (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (redirect : v14 s i = 0)
    (busy : s.g51.r1643_nio_5Fimem_5Fcache_5Fstate ≠ BitVec.ofNat 3 0) :
    (step s i).g51.r1645_nio_5Fimem_5Fcache_5FneedFlush =
      s.g51.r1645_nio_5Fimem_5Fcache_5FneedFlush := by
  change v25893 s i = _
  simp [v25893, v25803, reset, v25892, v25887, v25886, v2687,
    busy, v25891, v25890, v25889, v25888, v25815, v25814,
    v25813, v25812, v25811, v25810, v19, v18, v17, redirect, v16,
    v24, v4079]

theorem fetch_idle_without_capture_stays_idle (s : State) (i : Inputs)
    (idle : s.g51.r1643_nio_5Fimem_5Fcache_5Fstate = 0)
    (capture : v25943 s i ≠ 1) :
    (step s i).g51.r1643_nio_5Fimem_5Fcache_5Fstate = 0 := by
  have noRequest : v25808 s i ≠ 1 := by
    intro requested
    apply capture
    simp [v25943, v2689, v2688, idle, v2687, requested]
  have noStart : v25818 s i = 0 := by
    rcases BitVec.eq_zero_or_eq_one (v25808 s i) with zero | one
    · simp [v25818, v25809, zero]
    · exact False.elim (noRequest one)
  change v25883 s i = 0
  simp [v25883, v25882, v25804, idle, v2687, v25839, noStart]

theorem live_fetch_request_step (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (redirect : v14 s i = 0)
    (notDelivered : FetchNotAlreadyDelivered s) :
    LiveFetchRequest (step s i) ↔
      v25943 s i = 1 ∨ (LiveFetchRequest s ∧ v10241 s i = 0) := by
  constructor
  · intro live
    by_cases capture : v25943 s i = 1
    · exact Or.inl capture
    · right
      have busy : s.g51.r1643_nio_5Fimem_5Fcache_5Fstate ≠ 0 := by
        intro idle
        exact live.1 (fetch_idle_without_capture_stays_idle s i idle capture)
      have clear : s.g51.r1645_nio_5Fimem_5Fcache_5FneedFlush = 0 :=
        (fetch_busy_flush_flag_hold s i reset redirect busy).symm.trans live.2
      have noEnqueue : v10241 s i = 0 := by
        rcases BitVec.eq_zero_or_eq_one (v10241 s i) with zero | one
        · exact zero
        · exact False.elim (live.1 (fetch_enqueue_returns_idle s i one))
      exact ⟨⟨busy, clear⟩, noEnqueue⟩
  · intro source
    rcases source with capture | ⟨live, noEnqueue⟩
    · exact fetch_capture_becomes_live s i reset redirect capture
    · exact ⟨fetch_wait_stays_active s i reset live.1 live.2 notDelivered
        ((fetch_response_fire_eq_enqueue s i redirect).trans noEnqueue),
        (fetch_busy_flush_flag_hold s i reset redirect live.1).trans live.2⟩

#print axioms live_fetch_request_step
end NutShellProofs
