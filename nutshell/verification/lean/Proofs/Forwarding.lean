import Proofs.WritebackSelection

namespace NutShellProofs
open nNutCore

theorem commit_requires_execute_valid (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) : v6 s i = 1 := by
  rcases BitVec.eq_zero_or_eq_one (v6 s i) with h | h
  · have capture := commit_requires_capture s i next commit
    simp [v25332, v11702, v11701, h] at capture
  · exact h

theorem commit_requires_unflushed (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) : v23 s i = 0 := by
  rcases BitVec.eq_zero_or_eq_one (v23 s i) with h | h
  · exact h
  · have flush : v25328 s i = 1 := h
    change v25331 s i = 1 at commit
    simp [v25331, v25330, flush, v24] at commit

theorem forward_alu_result (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0) :
    v25103 s i = v25095 s i := by
  have valid := commit_requires_execute_valid s i next commit
  have flush := commit_requires_unflushed s i next commit
  simp [v25103, v25102, v25101, v25007, v25005, v25006, v110,
    v12140, v12139, v12137, v12138, v12136, v12135, v24, unit, valid, flush]

theorem forward_lsu_result (s : State) (i : Inputs) (unit : v3 s i = 1) :
    v25103 s i = v25100 s i := by
  simp [v25103, v25102, v25101, v25007, v25005, v25006, v110,
    v12140, v12139, v12137, v12136, v12135, unit]

-- ISU's execute-forward value equals the following committed writeback value.
theorem forward_matches_writeback (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0 ∨ v3 s i = 1) :
    v25103 s i = v11842 (step s i) next := by
  rcases unit with alu | lsu
  · rw [writeback_capture_0 s i next commit alu]
    exact forward_alu_result s i next commit alu
  · rw [writeback_capture_1 s i next commit lsu]
    exact forward_lsu_result s i lsu

#print axioms forward_matches_writeback
end NutShellProofs
