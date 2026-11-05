import Proofs.TrapRedirect
namespace NutShellProofs
open nNutCore

/-- The actual branch predictor correction condition, including direction. -/
theorem branch_redirect_condition (s : State) (i : Inputs) (operation : BranchOp)
    (op : v28 s i = operation.control) :
    v12218 s i =
      if v12179 s i = 0 then v12186 s i
      else (if v12186 s i = 0 then 1 else 0) |||
        (if v12212 s i ≠ v12215 s i then 1 else 0) := by
  have branch : v12182 s i = 1 := by
    cases operation <;> simp [v12182, v12181, v12141, op, BranchOp.control, v24]
  rcases BitVec.eq_zero_or_eq_one (v12179 s i) with h | h <;>
    simp [v12218, v12183, v12180, branch, h, v24, v12217,
      v12188, v12187, v12186, v12216, v12213]

theorem committed_branch_redirect_valid (s : State) (i next : Inputs)
    (operation : BranchOp) (op : v28 s i = operation.control)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0)
    (noTrap : v13725 s i = 0) :
    v8 (step s i) next = v12218 s i := by
  obtain ⟨mou, csr⟩ := alu_redirect_priority s i unit
  have noCSR := csr.trans noTrap
  have valid := commit_requires_execute_valid s i next commit
  have flush := commit_requires_unflushed s i next commit
  have branchBit : v12142 s i = 1 := by
    cases operation <;> simp [v12142, v12141, op, BranchOp.control]
  change v25388 s i = _
  rcases BitVec.eq_zero_or_eq_one (v12218 s i) with h | h <;>
    simp [h, v25388, commit_requires_capture s i next commit, v25387, v25386,
    mou, v25385, noCSR, v25384, v25383, v25382, branchBit,
    v12140, v12139, v12138, v12137, v12136, v12135, unit, valid, flush, v24]

/-- At commit the actual backend flush bit is the captured redirect-valid bit. -/
theorem commit_flush_eq_redirect (s : State) (i : Inputs) (commit : v9 s i = 1) :
    v23 s i = v8 s i := by
  rcases BitVec.eq_zero_or_eq_one (v8 s i) with h | h <;>
    simp [v23, v22, v21, v20, v19, v18, v17, v14, v13, v12, v11,
      v10, commit, h, v15, v16]


/-- Consecutive commits require the earlier branch correction condition to be zero. -/
theorem consecutive_branch_prediction_accepted (s : State) (i next after : Inputs)
    (operation : BranchOp) (op : v28 s i = operation.control)
    (unit : v3 s i = 0) (commit : v9 (step s i) next = 1)
    (following : v9 (step (step s i) next) after = 1) :
    v12218 s i = 0 := by
  have flush := commit_requires_unflushed (step s i) next after following
  have captured := committed_branch_redirect_valid s i next operation op commit unit
    (consecutive_commits_no_trap s i next after commit following)
  exact captured.symm.trans ((commit_flush_eq_redirect (step s i) next commit).symm.trans flush)

/-- For a taken branch, acceptance checks both direction and target address. -/
theorem accepted_taken_branch_prediction (s : State) (i : Inputs)
    (operation : BranchOp) (op : v28 s i = operation.control)
    (taken : v12179 s i = 1) (accepted : v12218 s i = 0) :
    v12186 s i = 1 ∧ v12212 s i = v12215 s i := by
  have condition := branch_redirect_condition s i operation op
  rw [accepted] at condition
  rcases BitVec.eq_zero_or_eq_one (v12186 s i) with h | h <;>
    by_cases addr : v12212 s i = v12215 s i <;>
    simp [taken, h, addr] at condition ⊢


theorem accepted_untaken_branch_prediction (s : State) (i : Inputs)
    (operation : BranchOp) (op : v28 s i = operation.control)
    (taken : v12179 s i = 0) (accepted : v12218 s i = 0) :
    v12186 s i = 0 := by
  have condition := branch_redirect_condition s i operation op
  simpa [taken, accepted] using condition.symm

#print axioms accepted_untaken_branch_prediction
#print axioms consecutive_branch_prediction_accepted
#print axioms accepted_taken_branch_prediction
#print axioms branch_redirect_condition
#print axioms committed_branch_redirect_valid
#print axioms commit_flush_eq_redirect
end NutShellProofs
