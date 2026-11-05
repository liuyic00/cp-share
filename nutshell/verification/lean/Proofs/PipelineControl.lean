import Proofs.IssuedRegisterOperands
namespace NutShellProofs
open nNutCore

theorem execute_flush_bits_agree (s : State) (i : Inputs) : v23 s i = v11458 s i := by
  rcases BitVec.eq_zero_or_eq_one (v14 s i) with h | h <;>
    simp [v23, v22, v11458, v11457, v21, v20, v19, v18, v17, h, v15, v16]

theorem next_valid_controls (s : State) (i next : Inputs)
    (valid : v6 (step s i) next = 1) : i.g0.nreset = 0 ∧ v23 s i = 0 := by
  have reset : i.g0.nreset = 0 := by
    rcases BitVec.eq_zero_or_eq_one i.g0.nreset with h | h
    · exact h
    · rw [execute_valid_reset s i next h] at valid
      contradiction
  refine ⟨reset, ?_⟩
  rw [execute_flush_bits_agree]
  rcases BitVec.eq_zero_or_eq_one (v11458 s i) with h | h
  · exact h
  · have flush : v24276 s i = 1 := h
    change v24282 s i = 1 at valid
    simp [v24282, v11455, reset, v24281, flush, v24] at valid

theorem next_commit_controls (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) : i.g0.nreset = 0 ∧ v23 s i = 0 := by
  refine ⟨?_, commit_requires_unflushed s i next commit⟩
  rcases BitVec.eq_zero_or_eq_one i.g0.nreset with h | h
  · exact h
  · change v25331 s i = 1 at commit
    simp [v25331, v11455, h, v24] at commit

theorem issued_operand_1_at_next_commit (s : State) (i next later : Inputs)
    (invariant : ExecuteDestinationBusy s) (fire : v24283 s i = 1)
    (kind : v24881 s i = 0) (commit : v9 (step (step s i) next) later = 1) :
    (step s i).g48.r1564_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc1 =
      dutRead.v25201 (step (step s i) next) later (v11723 s i) := by
  have valid := commit_requires_execute_valid (step s i) next later commit
  obtain ⟨reset, flush⟩ := next_valid_controls s i next valid
  obtain ⟨nextReset, nextFlush⟩ := next_commit_controls (step s i) next later commit
  exact issued_operand_1_after_older_writeback s i next later invariant fire kind
    reset nextReset flush nextFlush

#print axioms issued_operand_1_at_next_commit

theorem issued_operand_2_at_next_commit (s : State) (i next later : Inputs)
    (invariant : ExecuteDestinationBusy s) (fire : v24283 s i = 1)
    (kind : v24896 s i = 0) (commit : v9 (step (step s i) next) later = 1) :
    (step s i).g48.r1565_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc2 =
      dutRead.v25201 (step (step s i) next) later (v11765 s i) := by
  have valid := commit_requires_execute_valid (step s i) next later commit
  obtain ⟨reset, flush⟩ := next_valid_controls s i next valid
  obtain ⟨nextReset, nextFlush⟩ := next_commit_controls (step s i) next later commit
  exact issued_operand_2_after_older_writeback s i next later invariant fire kind
    reset nextReset flush nextFlush

#print axioms issued_operand_2_at_next_commit
end NutShellProofs
