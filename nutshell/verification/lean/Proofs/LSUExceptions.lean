import Proofs.OperandWritebackView
namespace NutShellProofs
open nNutCore

theorem lsu_fault_raises_exception (s : State) (i : Inputs)
    (fault : v11632 s i = 1 ∨ v11638 s i = 1) : v13684 s i = 1 := by
  have nonzero : v13683 s i ≠ v9740 s i := by
    intro zero
    rcases fault with load | store
    · have bit : (v13683 s i).getLsbD 4 = true := by
        simp only [v13683, v13682, v13681, v13669, v13668, v13667,
          BitVec.getLsbD_or, BitVec.getLsbD_append]
        simp [load]
      rw [zero] at bit
      simp [v9740] at bit
    · have bit : (v13683 s i).getLsbD 6 = true := by
        simp only [v13683, v13682, v13681, v13669, v13664, v13663,
          BitVec.getLsbD_or, BitVec.getLsbD_append]
        simp [store]
      rw [zero] at bit
      simp [v9740] at bit
  rw [v13684, if_pos nonzero]

theorem exception_redirect (s : State) (i : Inputs)
    (raised : v13684 s i = 1) (valid : v6 s i = 1) (flush : v23 s i = 0) :
    v25387 s i = 1 := by
  have instrValid : v13724 s i = 1 := by
    simp [v13724, v13723, v13722, v24, valid, flush]
  have either : v13721 s i = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v13720 s i) with h | h <;>
      simp [v13721, raised, h]
  have trap : v13725 s i = 1 := by simp [v13725, either, instrValid]
  have csr : v25354 s i = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v25348 s i) with h | h <;>
      rcases BitVec.eq_zero_or_eq_one (v25352 s i) with k | k <;>
        simp [v25354, v25353, v25349, trap, h, k]
  by_cases mou : v25339 s i = 1
  · simp only [v25387, v25386, mou, ↓reduceIte]
  · simp only [v25387, v25386, mou, ↓reduceIte, v25385, csr]

theorem lsu_fault_flushes_next (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1)
    (fault : v11632 s i = 1 ∨ v11638 s i = 1) : v23 (step s i) next = 1 := by
  have valid := commit_requires_execute_valid s i next commit
  have unflushed := commit_requires_unflushed s i next commit
  have redirect := exception_redirect s i (lsu_fault_raises_exception s i fault) valid unflushed
  have redirectNext : v8 (step s i) next = 1 := by
    change v25388 s i = 1
    rw [v25388, if_pos (commit_requires_capture s i next commit), redirect]
  simp [v23, v22, v21, v20, v19, v18, v17, v14, v13, v12, v11,
    v10, commit, redirectNext, v15]

theorem next_unflushed_lsu_has_no_fault (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (flush : v23 (step s i) next = 0) :
    v11632 s i = 0 ∧ v11638 s i = 0 := by
  constructor
  · rcases BitVec.eq_zero_or_eq_one (v11632 s i) with zero | one
    · exact zero
    · have bad := lsu_fault_flushes_next s i next commit (Or.inl one)
      rw [flush] at bad
      contradiction
  · rcases BitVec.eq_zero_or_eq_one (v11638 s i) with zero | one
    · exact zero
    · have bad := lsu_fault_flushes_next s i next commit (Or.inr one)
      rw [flush] at bad
      contradiction

theorem lsu_next_writeback_enabled (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 1)
    (write : v11475 s i = 1) (nextFlush : v23 (step s i) next = 0) :
    v11462 (step s i) next = 1 := by
  obtain ⟨loadOK, storeOK⟩ := next_unflushed_lsu_has_no_fault s i next commit nextFlush
  have notCSR : v13180 s i = 0 := by
    simp [v13180, v13178, v13177, v13176, unit]
  have noFault : v25477 s i = 1 := by
    simp [v25477, v25475, v25473, v25472, v25471, v25474, v25476,
      loadOK, storeOK, v24]
  have allowed : v25479 s i = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v25478 s i) with h | h <;>
      simp [v25479, noFault, h]
  have wen : v11473 s i = 1 := write
  have emitted : v25485 s i = 1 := by
    simp [v25485, v25484, v25480, wen, allowed, v25483, v25482, notCSR, v24]
  have nextWen : v11459 (step s i) next = 1 :=
    (capture_decode_ctrl_rfWen s i next commit).trans emitted
  simp [v11462, v11461, v11460, nextWen, commit]

#print axioms lsu_next_writeback_enabled
#print axioms lsu_fault_flushes_next
#print axioms next_unflushed_lsu_has_no_fault
end NutShellProofs
