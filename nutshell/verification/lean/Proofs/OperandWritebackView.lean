import Proofs.WritebackOrigin
namespace NutShellProofs
open nNutCore

theorem issued_non_execute_operand_1_after_older_writeback (s : State) (i next later : Inputs)
    (invariant : ExecuteDestinationBusy s) (fire : v24283 s i = 1)
    (noEx : v11741 s i = 0) (kind : v24881 s i = 0)
    (reset : i.g0.nreset = 0) (nextReset : next.g0.nreset = 0) :
    (step s i).g48.r1564_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc1 =
      dutRead.v25201 (step (step s i) next) later (v11723 s i) := by
  rw [issued_non_execute_operand_1 s i next invariant fire noEx kind reset]
  rw [dut_read_step (step s i) next later _ nextReset]
  by_cases zero : v11723 s i = 0
  · rw [if_pos zero, zero, dutRead.read_0]
  · have noMatch : ¬(v11465 (step s i) next = v11723 s i ∧ v11462 (step s i) next = 1) := by
      intro ⟨dest, write⟩
      obtain ⟨valid, wen, origin⟩ := next_writeback_origin s i next write
      have same : v11723 s i = v11470 s i := dest.symm.trans origin
      have forward := issue_dependency_1_forwards s i invariant fire valid wen zero same
      rw [noEx] at forward
      contradiction
    rw [if_neg zero, if_neg noMatch]

#print axioms issued_non_execute_operand_1_after_older_writeback
theorem issued_non_execute_operand_2_after_older_writeback (s : State) (i next later : Inputs)
    (invariant : ExecuteDestinationBusy s) (fire : v24283 s i = 1)
    (noEx : v11776 s i = 0) (kind : v24896 s i = 0)
    (reset : i.g0.nreset = 0) (nextReset : next.g0.nreset = 0) :
    (step s i).g48.r1565_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc2 =
      dutRead.v25201 (step (step s i) next) later (v11765 s i) := by
  rw [issued_non_execute_operand_2 s i next invariant fire noEx kind reset]
  rw [dut_read_step (step s i) next later _ nextReset]
  by_cases zero : v11765 s i = 0
  · rw [if_pos zero, zero, dutRead.read_0]
  · have noMatch : ¬(v11465 (step s i) next = v11765 s i ∧ v11462 (step s i) next = 1) := by
      intro ⟨dest, write⟩
      obtain ⟨valid, wen, origin⟩ := next_writeback_origin s i next write
      have same : v11765 s i = v11470 s i := dest.symm.trans origin
      have forward := issue_dependency_2_forwards s i invariant fire valid wen zero same
      rw [noEx] at forward
      contradiction
    rw [if_neg zero, if_neg noMatch]

#print axioms issued_non_execute_operand_2_after_older_writeback
theorem issued_operand_1_after_alu_writeback (s : State) (i next later : Inputs)
    (invariant : ExecuteDestinationBusy s) (fire : v24283 s i = 1)
    (kind : v24881 s i = 0) (unit : v3 s i = 0)
    (reset : i.g0.nreset = 0) (nextReset : next.g0.nreset = 0) (flush : v23 s i = 0) :
    (step s i).g48.r1564_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc1 =
      dutRead.v25201 (step (step s i) next) later (v11723 s i) := by
  rcases BitVec.eq_zero_or_eq_one (v11741 s i) with noEx | forward
  · exact issued_non_execute_operand_1_after_older_writeback s i next later
      invariant fire noEx kind reset nextReset
  · obtain ⟨nonzero, same, enabled⟩ := execute_forward_1_matches s i forward
    have valid : v6 s i = 1 := by
      rcases BitVec.eq_zero_or_eq_one (v6 s i) with h | h
      · simp [v11478, v11477, v11476, h] at enabled
      · exact h
    have wen : v11475 s i = 1 := by
      rcases BitVec.eq_zero_or_eq_one (v11475 s i) with h | h
      · simp [v11478, h] at enabled
      · exact h
    have commit := issue_with_valid_execute_commits s i next fire valid reset flush
    have write := alu_next_writeback_enabled s i next commit unit wen
    have dest : v11465 (step s i) next = v11723 s i :=
      (capture_decode_ctrl_rfDest s i next commit).trans same.symm
    rw [issued_forward_1_equals_writeback s i next fire forward kind reset flush,
      dut_read_step (step s i) next later _ nextReset, if_neg nonzero, if_pos ⟨dest, write⟩]

#print axioms issued_operand_1_after_alu_writeback
theorem issued_operand_2_after_alu_writeback (s : State) (i next later : Inputs)
    (invariant : ExecuteDestinationBusy s) (fire : v24283 s i = 1)
    (kind : v24896 s i = 0) (unit : v3 s i = 0)
    (reset : i.g0.nreset = 0) (nextReset : next.g0.nreset = 0) (flush : v23 s i = 0) :
    (step s i).g48.r1565_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc2 =
      dutRead.v25201 (step (step s i) next) later (v11765 s i) := by
  rcases BitVec.eq_zero_or_eq_one (v11776 s i) with noEx | forward
  · exact issued_non_execute_operand_2_after_older_writeback s i next later
      invariant fire noEx kind reset nextReset
  · obtain ⟨nonzero, same, enabled⟩ := execute_forward_2_matches s i forward
    have valid : v6 s i = 1 := by
      rcases BitVec.eq_zero_or_eq_one (v6 s i) with h | h
      · simp [v11478, v11477, v11476, h] at enabled
      · exact h
    have wen : v11475 s i = 1 := by
      rcases BitVec.eq_zero_or_eq_one (v11475 s i) with h | h
      · simp [v11478, h] at enabled
      · exact h
    have commit := issue_with_valid_execute_commits s i next fire valid reset flush
    have write := alu_next_writeback_enabled s i next commit unit wen
    have dest : v11465 (step s i) next = v11765 s i :=
      (capture_decode_ctrl_rfDest s i next commit).trans same.symm
    rw [issued_forward_2_equals_writeback s i next fire forward kind reset flush,
      dut_read_step (step s i) next later _ nextReset, if_neg nonzero, if_pos ⟨dest, write⟩]

#print axioms issued_operand_2_after_alu_writeback
end NutShellProofs
