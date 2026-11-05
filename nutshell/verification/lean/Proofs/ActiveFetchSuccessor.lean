import Proofs.FetchPCTransition
namespace NutShellProofs
open nNutCore

def ActiveFetchSuccessor (s : State) : Prop :=
  s.g51.r1643_nio_5Fimem_5Fcache_5Fstate ≠ 0 →
  s.g51.r1645_nio_5Fimem_5Fcache_5FneedFlush = 0 →
  BitVec.extractLsb' 39 39 s.g51.r1656_nio_5Fimem_5Fcache_5Fmemuser =
    s.g33.r1065_nfrontend_5Fifu_5Fpc

theorem active_fetch_successor_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    ActiveFetchSuccessor (step s i) := by
  intro active
  change v25883 s i ≠ 0 at active
  simp [v25883, v25803, reset, v2687] at active

theorem active_fetch_successor_step (s : State) (i : Inputs)
    (old : ActiveFetchSuccessor s) : ActiveFetchSuccessor (step s i) := by
  intro active clear
  have reset : i.g0.nreset = 0 := by
    rcases BitVec.eq_zero_or_eq_one i.g0.nreset with zero | one
    · exact zero
    · change v25883 s i ≠ 0 at active
      simp [v25883, v25803, one, v2687] at active
  by_cases capture : v25943 s i = 1
  · have redirect : v14 s i = 0 := by
      rcases BitVec.eq_zero_or_eq_one (v14 s i) with zero | one
      · exact zero
      · exact False.elim (active (redirected_fetch_capture_stays_idle s i capture one))
    exact fetch_capture_successor_matches_next_pc s i reset redirect capture
  · have busy : s.g51.r1643_nio_5Fimem_5Fcache_5Fstate ≠ 0 := by
      intro idle
      have noRequest : v25808 s i ≠ 1 := by
        intro requested
        apply capture
        simp [v25943, v2689, v2688, idle, v2687, requested]
      have noStart : v25818 s i = 0 := by
        rcases BitVec.eq_zero_or_eq_one (v25808 s i) with zero | one
        · simp [v25818, v25809, zero]
        · exact False.elim (noRequest one)
      change v25883 s i ≠ 0 at active
      simp [v25883, v25882, v25804, idle, v2687, v25839, noStart] at active
    have busyLiteral : s.g51.r1643_nio_5Fimem_5Fcache_5Fstate ≠ BitVec.ofNat 3 0 := busy
    have clearNext : v25893 s i = 0 := clear
    have redirect : v14 s i = 0 := by
      rcases BitVec.eq_zero_or_eq_one (v14 s i) with zero | one
      · exact zero
      · simp [v25893, v25803, reset, v25892, v25887, v25886, v2687,
          busyLiteral, v25891, v25890, v25889, v25888, v25815, v25814,
          v25813, v25812, v25811, v25810, v19, v18, v17, one, v15,
          v24, v2750, v110] at clearNext
    have oldClear : s.g51.r1645_nio_5Fimem_5Fcache_5FneedFlush = 0 := by
      simpa [v25893, v25803, reset, v25892, v25887, v25886, v2687,
        busyLiteral, v25891, v25890, v25889, v25888, v25815, v25814,
        v25813, v25812, v25811, v25810, v19, v18, v17, redirect, v16,
        v24, v4079] using clearNext
    have metadata : (step s i).g51.r1656_nio_5Fimem_5Fcache_5Fmemuser =
        s.g51.r1656_nio_5Fimem_5Fcache_5Fmemuser := by
      change v25966 s i = _
      rw [v25966, if_neg capture]
    rw [metadata, fetch_pc_transition]
    simpa only [reset, redirect, if_neg capture, show (0 : BitVec 1) ≠ 1 by decide,
      ↓reduceIte] using old busy oldClear

theorem active_fetch_successor_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    ActiveFetchSuccessor (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact active_fetch_successor_reset initial (inputs 0) reset
  | succ t ih => exact active_fetch_successor_step _ _ ih

#print axioms active_fetch_successor_run

theorem fetch_enqueue_successor_is_ifu_pc (s : State) (i : Inputs)
    (invariant : ActiveFetchSuccessor s) (enqueue : v10241 s i = 1) :
    v10273 s i = s.g33.r1065_nfrontend_5Fifu_5Fpc := by
  have clear : s.g51.r1645_nio_5Fimem_5Fcache_5FneedFlush = 0 := by
    rcases BitVec.eq_zero_or_eq_one s.g51.r1645_nio_5Fimem_5Fcache_5FneedFlush with zero | one
    · exact zero
    · simp [v10241, v10240, v10239, v10238, v10237, v10236,
        v9709, v9708, v9707, v9706, v9705, v9704, v9703, v24, one] at enqueue
  have successor := invariant (fetch_enqueue_requires_active_response s i enqueue) clear
  have slice : ∀ x : BitVec 87, BitVec.extractLsb' 39 39 (BitVec.extractLsb' 0 82 x) = BitVec.extractLsb' 39 39 x := by
    intro x
    apply BitVec.eq_of_getLsbD_eq
    intro k
    simp only [BitVec.getLsbD_extractLsb']
    by_cases small : k < 39
    · have bound : 39 + k < 82 := by omega
      simp [small, bound]
    · simp [small]
  simpa [v10273, v10272, v10271, v10262, v10261, v10260, v10259,
    v10258, v10257, slice] using successor

#print axioms fetch_enqueue_successor_is_ifu_pc
end NutShellProofs
