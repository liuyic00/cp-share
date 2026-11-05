import Proofs.FetchResponseTransfer
namespace NutShellProofs
open nNutCore

theorem fetch_response_fire_returns_idle (s : State) (i : Inputs)
    (fire : v25894 s i = 1) :
    (step s i).g51.r1643_nio_5Fimem_5Fcache_5Fstate = 0 := by
  have response : v9705 s i = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v9705 s i) with zero | one
    · simp [v25894, zero] at fire
    · exact one
  have state : s.g51.r1643_nio_5Fimem_5Fcache_5Fstate = BitVec.ofNat 3 5 := by
    by_cases state : s.g51.r1643_nio_5Fimem_5Fcache_5Fstate = BitVec.ofNat 3 5
    · exact state
    · simp [v9705, v9704, v9702, v9701, state] at response
  have transfer : v25873 s i = 1 := fire
  change v25883 s i = 0
  rcases BitVec.eq_zero_or_eq_one s.g51.r1645_nio_5Fimem_5Fcache_5FneedFlush with zero | one <;>
    rcases BitVec.eq_zero_or_eq_one s.g51.r1646_nio_5Fimem_5Fcache_5FalreadyOutFire with zero | one
  all_goals simp_all [v25883, v25882, v25804, v2687, v25881, v25840, v11531,
    v25880, v25846, v12711, v25879, v25851, v11537, v25878, v25860,
    v4, v25877, v25868, v9701, v25876, v25875, v25874]

def FetchNotAlreadyDelivered (s : State) : Prop :=
  s.g51.r1643_nio_5Fimem_5Fcache_5Fstate ≠ 0 →
    s.g51.r1646_nio_5Fimem_5Fcache_5FalreadyOutFire = 0

theorem fetch_not_delivered_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    FetchNotAlreadyDelivered (step s i) := by
  intro _
  change v25897 s i = 0
  simp [v25897, v25803, reset, v24]

theorem fetch_not_delivered_step (s : State) (i : Inputs)
    (old : FetchNotAlreadyDelivered s) : FetchNotAlreadyDelivered (step s i) := by
  intro active
  have noFire : v25894 s i ≠ 1 := by
    intro fire
    exact active (fetch_response_fire_returns_idle s i fire)
  change v25897 s i = 0
  by_cases idle : s.g51.r1643_nio_5Fimem_5Fcache_5Fstate = BitVec.ofNat 3 0
  · simp [v25897, v25896, v25804, v2687, idle, v24]
  · have clear := old idle
    simp only [v25897, v25896, v25895, if_neg noFire, clear, v24]
    split <;> simp

theorem fetch_not_delivered_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    FetchNotAlreadyDelivered (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact fetch_not_delivered_reset initial (inputs 0) reset
  | succ t ih => exact fetch_not_delivered_step _ _ ih

#print axioms fetch_not_delivered_run

/-- A live request cannot disappear without reset, flush, or response transfer. -/
theorem fetch_wait_stays_active (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0)
    (busy : s.g51.r1643_nio_5Fimem_5Fcache_5Fstate ≠ BitVec.ofNat 3 0)
    (clear : s.g51.r1645_nio_5Fimem_5Fcache_5FneedFlush = 0)
    (notDelivered : FetchNotAlreadyDelivered s)
    (noFire : v25894 s i = 0) :
    (step s i).g51.r1643_nio_5Fimem_5Fcache_5Fstate ≠ 0 := by
  have old := notDelivered busy
  have noTransfer : v25873 s i = 0 := noFire
  change v25883 s i ≠ 0
  simp only [v25883, v25803, reset, v25882, v25804, v2687,
    v25881, v25845, v25880, v25850, v25879, v25859,
    v25878, v25867, v25877, v25876, v25875, v25874,
    clear, old, noTransfer, v12711, v9701, v4]
  repeat (first | (solve | simp_all [Ne.symm busy]) | split)

#print axioms fetch_wait_stays_active

theorem fetch_response_fire_eq_enqueue (s : State) (i : Inputs)
    (noRedirect : v14 s i = 0) : v25894 s i = v10241 s i := by
  rcases BitVec.eq_zero_or_eq_one (v9705 s i) with zero | one
  all_goals simp_all [v25894, v25872, v25871, v25870, v25869, v9700, v9699, v2698,
    v9698, v18, v17, v16, v10241, v10240, v10239, v10238,
    v10237, v10236, v24, v9709, v9708, v9707, v9706]

theorem fetch_wait_stays_active_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (currentReset : (inputs (t + 1)).g0.nreset = 0)
    (busy : (run initial inputs (t + 1)).g51.r1643_nio_5Fimem_5Fcache_5Fstate ≠ 0)
    (clear : (run initial inputs (t + 1)).g51.r1645_nio_5Fimem_5Fcache_5FneedFlush = 0)
    (noRedirect : v14 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (noEnqueue : v10241 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    (run initial inputs (t + 2)).g51.r1643_nio_5Fimem_5Fcache_5Fstate ≠ 0 := by
  exact fetch_wait_stays_active _ _ currentReset busy clear
    (fetch_not_delivered_run initial inputs reset t)
    ((fetch_response_fire_eq_enqueue _ _ noRedirect).trans noEnqueue)

#print axioms fetch_wait_stays_active_run
end NutShellProofs
