import Proofs.MemoryRequestIdentity
import Proofs.PipelinePendingOrder
namespace NutShellProofs
open nNutCore

theorem incomplete_execute_has_no_next_commit (s : State) (i next : Inputs)
    (incomplete : v11702 s i = 0) : v9 (step s i) next = 0 := by
  change v25331 s i = 0
  simp [v25331, v25330, v25329, incomplete, v24]

theorem no_commit_has_no_execute_flush (s : State) (i : Inputs)
    (idle : v9 s i = 0) : v24276 s i = 0 := by
  rw [(pipeline_flush_signals s i).2.1]
  simp [v14, v13, v12, v11, v10, idle]

theorem normal_memory_next_busy_no_next_flush (s : State) (i next : Inputs)
    (operation : MemoryOp) (op : v28 s i = operation.control)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (reachable : LSUInnerReachable s) (unit : v3 s i = 1)
    (noFault : v11639 s i = 0) (aligned : v11640 s i = 0)
    (nextBusy : (step s i).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate ≠ 0) :
    v9 (step s i) next = 0 ∧ v24276 (step s i) next = 0 := by
  have incomplete : v11698 s i = 0 := by
    rcases BitVec.eq_zero_or_eq_one (v11698 s i) with zero | one
    · exact zero
    · exact False.elim (nextBusy (normal_memory_completion_returns_inner_idle s i
        operation op outer reachable noFault aligned one))
  have noComplete : v11702 s i = 0 := by
    simp [v11702, v11701, v11700, v11495, v11494, unit, v11699,
      v11518, v11517, incomplete]
  have noCommit := incomplete_execute_has_no_next_commit s i next noComplete
  exact ⟨noCommit, no_commit_has_no_execute_flush _ _ noCommit⟩
#print axioms incomplete_execute_has_no_next_commit
#print axioms no_commit_has_no_execute_flush
#print axioms normal_memory_next_busy_no_next_flush
end NutShellProofs
