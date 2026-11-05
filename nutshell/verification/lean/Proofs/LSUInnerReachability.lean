import Proofs.LSURequestState
namespace NutShellProofs
open nNutCore

def LSUInnerReachable (s : State) : Prop :=
  s.g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 0 ∨
  s.g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 2 ∨
  s.g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 3

theorem lsu_inner_reachable_step (s : State) (i : Inputs)
    (old : LSUInnerReachable s) : LSUInnerReachable (step s i) := by
  unfold LSUInnerReachable at old ⊢
  change v12276 s i = 0 ∨ v12276 s i = 2 ∨ v12276 s i = 3
  rcases old with idle | waiting | finishing
  all_goals
    simp only [v12276, v12275, v12236, v12265, v12274, v12266,
      v12273, v12267, v12270, v12269, v12272, v12271,
      v4079, v9721, v2750, v10089]
    simp only [*]
    repeat' split <;> simp_all

theorem lsu_inner_reachable_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) :
    LSUInnerReachable (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact Or.inl (lsu_inner_reset initial (inputs 0) reset)
  | succ t ih => exact lsu_inner_reachable_step _ _ ih
#print axioms lsu_inner_reachable_step
#print axioms lsu_inner_reachable_run
theorem lsu_inner_busy_predecessor (s : State) (i : Inputs)
    (busy : (step s i).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate ≠ 0) :
    s.g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate ≠ 0 ∨ v12570 s i = 1 := by
  by_cases idle : s.g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 0
  · right
    rcases BitVec.eq_zero_or_eq_one (v12570 s i) with noRequest | request
    · have zero : (step s i).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 0 := by
        change v12276 s i = 0
        have requestZero : v12263 s i = 0 := noRequest
        simp [v12276, v12275, v12236, v4079, idle, v12265, v12264, requestZero]
      exact False.elim (busy zero)
    · exact request
  · exact Or.inl idle

theorem lsu_inner_busy_has_prior_request (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (busy : (run initial inputs (t + 1)).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate ≠ 0) :
    ∃ k, k ≤ t ∧ v12570 (run initial inputs k) (inputs k) = 1 := by
  induction t with
  | zero => exact False.elim (busy (lsu_inner_reset initial (inputs 0) reset))
  | succ t ih =>
    rcases lsu_inner_busy_predecessor _ _ busy with prior | request
    · obtain ⟨k, bound, captured⟩ := ih prior
      exact ⟨k, by omega, captured⟩
    · exact ⟨t + 1, Nat.le_refl _, request⟩
#print axioms lsu_inner_busy_predecessor
#print axioms lsu_inner_busy_has_prior_request
end NutShellProofs
