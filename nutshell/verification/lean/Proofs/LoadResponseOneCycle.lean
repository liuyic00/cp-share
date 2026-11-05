import Proofs.ReferenceLoadDataCapture
namespace NutShellProofs
open nNutCore

theorem lsu_response_cache_conditions (s : State) (i : Inputs)
    (response : v11661 s i = 1) :
    s.g51.r1642_ndmemXbar_5FinflightSrc = 0 ∧
    s.g51.r1661_nio_5Fdmem_5Fcache_5Fstate = 5 ∧
    s.g51.r1663_nio_5Fdmem_5Fcache_5FneedFlush = 0 := by
  by_cases route : (0#2) = s.g51.r1642_ndmemXbar_5FinflightSrc <;>
    by_cases state : s.g51.r1661_nio_5Fdmem_5Fcache_5Fstate = 5#3 <;>
    by_cases flush : s.g51.r1663_nio_5Fdmem_5Fcache_5FneedFlush = 0#1 <;>
    simp [route, state, flush, v11661, v11660, v11659, v11658, v11657, v11656, v11655,
      v11654, v11653, v11652, v11651, v11650, v11649, v11648, v11647,
      v9701, v24] at response
  exact ⟨route.symm, state, flush⟩

theorem lsu_response_returns_cache_idle (s : State) (i : Inputs)
    (response : v11661 s i = 1) :
    (step s i).g51.r1661_nio_5Fdmem_5Fcache_5Fstate = 0 := by
  obtain ⟨route, state, flush⟩ := lsu_response_cache_conditions s i response
  have ready : v25784 s i = 1 := by
    simp [v25784, v25783, v25782, v25781, v25780, v25779, v25778,
      v25777, v25776, v25775, v25774, v25773, v25772, v25771, v25768,
      v25767, v25764, v25762, route, v2750, v9721, v11646, v110]
  change v26041 s i = 0
  simp [v26041, v26040, v25988, v26039, v26000, v26038, v26006,
    v26037, v26011, v26036, v26021, v26035, v26029, v26034,
    v26033, v26032, v26031, v26030, ready, v11652, v11651,
    v11649, v11650, state, flush, v9701, v24, v2687, v11531, v12711, v11537, v4]

  intro _
  rcases BitVec.eq_zero_or_eq_one s.g52.r1664_nio_5Fdmem_5Fcache_5FalreadyOutFire with h | h <;> simp [h]

theorem lsu_response_not_repeated (s : State) (i next : Inputs)
    (response : v11661 s i = 1) : v11661 (step s i) next = 0 := by
  have idle := lsu_response_returns_cache_idle s i response
  simp [v11661, v11660, v11659, v11658, v11657, v11656, v11655,
    v11654, v11653, v11652, v11651, v11649, idle, v9701, v24]
#print axioms lsu_response_returns_cache_idle
#print axioms lsu_response_not_repeated
theorem load_subword_cycle_has_no_new_response (s : State) (i next : Inputs)
    (extra : (step s i).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 3) :
    v11661 (step s i) next = 0 := by
  exact lsu_response_not_repeated s i next (load_subword_cycle_predecessor s i extra).2.2.1
#print axioms load_subword_cycle_has_no_new_response
end NutShellProofs
