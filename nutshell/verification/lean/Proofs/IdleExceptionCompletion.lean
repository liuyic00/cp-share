import Proofs.MemoryExceptionSources
import Proofs.PipelinePendingOrder
namespace NutShellProofs
open nNutCore

/-- A complete unflushed execution is recorded as a commit outside reset. -/
theorem complete_execute_commits (s : State) (i next : Inputs)
    (reset : i.g0.nreset = 0) (flush : v23 s i = 0)
    (complete : v11702 s i = 1) : v9 (step s i) next = 1 := by
  have same : v25328 s i = v23 s i := by
    rcases BitVec.eq_zero_or_eq_one (v14 s i) with clear | active <;>
      simp [v25328, v23, v22, v21, v20, v19, v18, v17, v15, v16, *]
  change v25331 s i = 1
  simp [v25331, v11455, reset, v25330, same, flush, v25329, complete, v11492, v110]

/-- LSU alignment faults complete immediately, without waiting for memory. -/
theorem faulting_lsu_completes (s : State) (i : Inputs)
    (valid : v6 s i = 1) (unit : v3 s i = 1)
    (fault : v11632 s i = 1 ∨ v11638 s i = 1) : v11702 s i = 1 := by
  rcases BitVec.eq_zero_or_eq_one (v11632 s i) with loadFault | loadFault <;>
    rcases BitVec.eq_zero_or_eq_one (v11638 s i) with storeFault | storeFault <;>
    simp_all [v11702, v11701, valid, v11700, v11495, v11494, unit,
      v11699, v11518, v11517, v11698, v11697, v11639, v110]

/-- Therefore an idle next cycle excludes both faults for an active unflushed LSU. -/
theorem idle_next_lsu_no_fault (s : State) (i next : Inputs)
    (reset : i.g0.nreset = 0) (flush : v23 s i = 0)
    (valid : v6 s i = 1) (unit : v3 s i = 1)
    (idle : v9 (step s i) next = 0) : v11632 s i = 0 ∧ v11638 s i = 0 := by
  have excluded : ¬ (v11632 s i = 1 ∨ v11638 s i = 1) := by
    intro fault
    have commit := complete_execute_commits s i next reset flush (faulting_lsu_completes s i valid unit fault)
    rw [idle] at commit
    contradiction
  rcases BitVec.eq_zero_or_eq_one (v11632 s i) with a | a <;>
    rcases BitVec.eq_zero_or_eq_one (v11638 s i) with b | b <;> simp_all
/-- ALU execution also completes immediately. -/
theorem active_alu_completes (s : State) (i : Inputs)
    (valid : v6 s i = 1) (unit : v3 s i = 0) : v11702 s i = 1 := by
  simp [v11702, v11701, valid, v11700, v11495, v11494, unit,
    v11699, v11518, v11517, v110]

/-- With no next commit, ALU cannot have been both valid and unflushed. -/
theorem idle_next_alu_inactive (s : State) (i next : Inputs)
    (reset : i.g0.nreset = 0) (unit : v3 s i = 0)
    (idle : v9 (step s i) next = 0) : v13724 s i = 0 := by
  rcases BitVec.eq_zero_or_eq_one (v6 s i) with valid | valid
  · simp [v13724, v13723, valid]
  · rcases BitVec.eq_zero_or_eq_one (v23 s i) with flush | flush
    · have commit := complete_execute_commits s i next reset flush (active_alu_completes s i valid unit)
      rw [idle] at commit
      contradiction
    · simp [v13724, v13723, v13722, flush, v24]
#print axioms active_alu_completes
#print axioms idle_next_alu_inactive
#print axioms complete_execute_commits
#print axioms faulting_lsu_completes
#print axioms idle_next_lsu_no_fault
end NutShellProofs
