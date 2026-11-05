import Proofs.MemoryRequestHold
namespace NutShellProofs
open nNutCore

theorem normal_memory_completion_returns_inner_idle (s : State) (i : Inputs)
    (operation : MemoryOp) (op : v28 s i = operation.control)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (reachable : LSUInnerReachable s)
    (noFault : v11639 s i = 0) (aligned : v11640 s i = 0)
    (complete : v11698 s i = 1) :
    (step s i).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 0 := by
  have notSC : v11673 s i = 0 := by
    cases operation <;> simp [v11673, v11526, op, MemoryOp.control, v11672]
  have result : v11665 s i = 1 := by
    simpa [v11698, v11697, noFault, v11696, v11519, outer, v2687,
      v11676, v11675, v11674, notSC, v11667, v11666, aligned] using complete
  change v12276 s i = 0
  rcases reachable with idle | waiting | finishing
  all_goals
    rcases BitVec.eq_zero_or_eq_one (v11644 s i) with subword | subword <;>
      rcases BitVec.eq_zero_or_eq_one (v11661 s i) with response | response
    all_goals
      simp_all [v11665, v11645, v11664, v11663, v11662, v11646, v110,
        v12276, v12275, v12236, v12265, v12274, v12266, v12273, v12267,
        v12270, v12269, v12268, v12272, v12271, v4079, v9721, v2750, v10089]
#print axioms normal_memory_completion_returns_inner_idle
theorem normal_memory_commit_inner_idle_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (noFault : v11639 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (aligned : v11640 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    (run initial inputs (t + 2)).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 0 := by
  have op := ((memory_decode_run initial inputs reset t).2
    (commit_requires_execute_valid _ _ _ commit) operation matched unit).1
  exact normal_memory_completion_returns_inner_idle _ _ operation op
    (original_assumptions_lsu_idle_run initial inputs reset environment t)
    (lsu_inner_reachable_run initial inputs reset t) noFault aligned
    (lsu_commit_requires_completion _ _ _ unit commit)
#print axioms normal_memory_commit_inner_idle_run
end NutShellProofs
