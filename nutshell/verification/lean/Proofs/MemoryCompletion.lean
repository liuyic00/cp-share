import Proofs.LSUInnerReachability
namespace NutShellProofs
open nNutCore

theorem memory_idle_without_fault_cannot_complete (s : State) (i : Inputs)
    (operation : MemoryOp) (op : v28 s i = operation.control)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (inner : s.g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 0)
    (noFault : v11639 s i = 0) (aligned : v11640 s i = 0) :
    v11698 s i = 0 := by
  have notSC : v11673 s i = 0 := by
    cases operation <;> simp [v11673, v11526, op, MemoryOp.control, v11672]
  simp [v11698, v11697, noFault, v11696, v11519, outer, v2687,
    v11676, v11675, v11674, notSC, v11667, v11666, aligned,
    v11665, v11645, v11664, v11663, inner, v2750, v9721]

theorem memory_normal_completion_has_prior_request (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (noFault : v11639 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (aligned : v11640 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (complete : v11698 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    ∃ k, k ≤ t ∧ v12570 (run initial inputs k) (inputs k) = 1 := by
  apply lsu_inner_busy_has_prior_request initial inputs reset t
  intro idle
  have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
  have zero := memory_idle_without_fault_cannot_complete _ _ operation op
    (original_assumptions_lsu_idle_run initial inputs reset environment t) idle noFault aligned
  rw [zero] at complete
  contradiction
#print axioms memory_idle_without_fault_cannot_complete
#print axioms memory_normal_completion_has_prior_request
theorem lsu_commit_requires_completion (s : State) (i next : Inputs)
    (unit : v3 s i = 1) (commit : v9 (step s i) next = 1) :
    v11698 s i = 1 := by
  have capture := commit_requires_capture s i next commit
  have valid := commit_requires_execute_valid s i next commit
  rcases BitVec.eq_zero_or_eq_one (v11698 s i) with zero | one
  · simp [zero, v25332, v11492, v110, v11702, v11701, valid, v11700,
    v11495, v11494, unit, v11699, v11518, v11517] at capture
  · exact one
#print axioms lsu_commit_requires_completion
end NutShellProofs
