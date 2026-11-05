import Proofs.OperandSelection

namespace NutShellProofs
open nNutCore

private theorem and_one_left (a b : BitVec 1) (h : a &&& b = 1) : a = 1 := by
  rcases BitVec.eq_zero_or_eq_one a with ha | ha
  · simp [ha] at h
  · exact ha

private theorem and_one_right (a b : BitVec 1) (h : a &&& b = 1) : b = 1 := by
  rcases BitVec.eq_zero_or_eq_one b with hb | hb
  · simp [hb] at h
  · exact hb

theorem issue_requires_ready (s : State) (i : Inputs) (fire : v24283 s i = 1) :
    v11751 s i = 1 ∧ v11786 s i = 1 := by
  have out := and_one_left _ _ fire
  have both : v11752 s i &&& v11786 s i = 1 := out
  exact ⟨and_one_right _ _ (and_one_left _ _ both), and_one_right _ _ both⟩

theorem issue_register_1_not_busy (s : State) (i : Inputs)
    (fire : v24283 s i = 1) (ex : v11741 s i = 0) (wb : v11750 s i = 0) :
    v11726 s i = 0 := by
  have ready := (issue_requires_ready s i fire).1
  rcases BitVec.eq_zero_or_eq_one (v11726 s i) with h | h
  · exact h
  · simp [v11751, v11742, v11727, v24, ex, wb, h] at ready

theorem issue_register_2_not_busy (s : State) (i : Inputs)
    (fire : v24283 s i = 1) (ex : v11776 s i = 0) (wb : v11785 s i = 0) :
    v11768 s i = 0 := by
  have ready := (issue_requires_ready s i fire).2
  rcases BitVec.eq_zero_or_eq_one (v11768 s i) with h | h
  · exact h
  · simp [v11786, v11777, v11769, v24, ex, wb, h] at ready

theorem execute_forward_1_matches (s : State) (i : Inputs)
    (forward : v11741 s i = 1) :
    v11723 s i ≠ 0 ∧ v11723 s i = v11470 s i ∧ v11478 s i = 1 := by
  have matched : v11732 s i = 1 := and_one_left _ _ forward
  have pair : v11731 s i = 1 := and_one_left _ _ matched
  have nz : v11729 s i = 1 := and_one_left _ _ pair
  have eq : v11730 s i = 1 := and_one_right _ _ pair
  have write : v11478 s i = 1 := and_one_right _ _ matched
  simp [v11729, v11728] at nz
  simp [v11730] at eq
  exact ⟨nz, eq, write⟩

theorem execute_forward_2_matches (s : State) (i : Inputs)
    (forward : v11776 s i = 1) :
    v11765 s i ≠ 0 ∧ v11765 s i = v11470 s i ∧ v11478 s i = 1 := by
  have matched : v11774 s i = 1 := and_one_left _ _ forward
  have pair : v11773 s i = 1 := and_one_left _ _ matched
  have nz : v11771 s i = 1 := and_one_left _ _ pair
  have eq : v11772 s i = 1 := and_one_right _ _ pair
  have write : v11478 s i = 1 := and_one_right _ _ matched
  simp [v11771, v11770] at nz
  simp [v11772] at eq
  exact ⟨nz, eq, write⟩

theorem issue_with_valid_execute_finishes (s : State) (i : Inputs)
    (fire : v24283 s i = 1) (valid : v6 s i = 1) : v11702 s i = 1 := by
  have ready : v11705 s i = 1 := and_one_right _ _ fire
  have done : (1 : BitVec 1) &&& v11702 s i = 1 := by
    simpa [v11705, v11704, v11491, v24, valid, v11703,
      v11493, v11492, v110] using ready
  exact and_one_right _ _ done

theorem issue_with_valid_execute_commits (s : State) (i next : Inputs)
    (fire : v24283 s i = 1) (valid : v6 s i = 1)
    (reset : i.g0.nreset = 0) (flush : v23 s i = 0) :
    v9 (step s i) next = 1 := by
  have done := issue_with_valid_execute_finishes s i fire valid
  have noFlush : v25328 s i = 0 := flush
  change v25331 s i = 1
  simp [v25331, v11455, v25330, v25329, v11492, v110,
    reset, noFlush, done]

private theorem forwardable_unit (s : State) (i : Inputs) (guard : v11739 s i = 0) :
    v3 s i = 0 ∨ v3 s i = 1 := by
  by_cases alu : v3 s i = 0
  · exact Or.inl alu
  by_cases lsu : v3 s i = 1
  · exact Or.inr lsu
  change ((if v3 s i ≠ 0 then (1 : BitVec 1) else 0) &&&
    (if v3 s i ≠ 1 then (1 : BitVec 1) else 0)) = 0 at guard
  rw [if_pos alu, if_pos lsu] at guard
  contradiction

theorem execute_forward_1_unit (s : State) (i : Inputs)
    (forward : v11741 s i = 1) : v3 s i = 0 ∨ v3 s i = 1 := by
  have guard : v11740 s i = 1 := and_one_right _ _ forward
  have allowed : v11739 s i = 0 := by simpa [v11740, v24] using guard
  exact forwardable_unit s i allowed

theorem issued_forward_1_equals_writeback (s : State) (i next : Inputs)
    (fire : v24283 s i = 1) (forward : v11741 s i = 1)
    (kind : v24881 s i = 0) (reset : i.g0.nreset = 0) (flush : v23 s i = 0) :
    (step s i).g48.r1564_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc1 =
      v11842 (step s i) next := by
  have enabled := (execute_forward_1_matches s i forward).2.2
  have valid : v6 s i = 1 := and_one_right _ _ enabled
  have commit := issue_with_valid_execute_commits s i next fire valid reset flush
  rw [operand_1_capture s i fire]
  exact operand_1_execute_writeback s i next kind forward commit
    (execute_forward_1_unit s i forward)

theorem writeback_forward_1_matches (s : State) (i : Inputs)
    (forward : v11750 s i = 1) :
    v11723 s i ≠ 0 ∧ v11723 s i = v11465 s i ∧ v11462 s i = 1 := by
  have matched : v11747 s i = 1 := and_one_left _ _ forward
  have pair : v11746 s i = 1 := and_one_left _ _ matched
  have nz : v11744 s i = 1 := and_one_left _ _ pair
  have eq : v11745 s i = 1 := and_one_right _ _ pair
  have write : v11462 s i = 1 := and_one_right _ _ matched
  simp [v11744, v11743] at nz
  simp [v11745] at eq
  exact ⟨nz, eq, write⟩

theorem writeback_forward_2_matches (s : State) (i : Inputs)
    (forward : v11785 s i = 1) :
    v11765 s i ≠ 0 ∧ v11765 s i = v11465 s i ∧ v11462 s i = 1 := by
  have matched : v11782 s i = 1 := and_one_left _ _ forward
  have pair : v11781 s i = 1 := and_one_left _ _ matched
  have nz : v11779 s i = 1 := and_one_left _ _ pair
  have eq : v11780 s i = 1 := and_one_right _ _ pair
  have write : v11462 s i = 1 := and_one_right _ _ matched
  simp [v11779, v11778] at nz
  simp [v11780] at eq
  exact ⟨nz, eq, write⟩

#print axioms issued_forward_1_equals_writeback
theorem execute_forward_2_unit (s : State) (i : Inputs)
    (forward : v11776 s i = 1) : v3 s i = 0 ∨ v3 s i = 1 := by
  have guard : v11775 s i = 1 := and_one_right _ _ forward
  have allowed : v11739 s i = 0 := by simpa [v11775, v24] using guard
  exact forwardable_unit s i allowed

theorem issued_forward_2_equals_writeback (s : State) (i next : Inputs)
    (fire : v24283 s i = 1) (forward : v11776 s i = 1)
    (kind : v24896 s i = 0) (reset : i.g0.nreset = 0) (flush : v23 s i = 0) :
    (step s i).g48.r1565_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc2 =
      v11842 (step s i) next := by
  have enabled := (execute_forward_2_matches s i forward).2.2
  have valid : v6 s i = 1 := and_one_right _ _ enabled
  have commit := issue_with_valid_execute_commits s i next fire valid reset flush
  rw [operand_2_capture s i fire]
  exact operand_2_execute_writeback s i next kind forward commit
    (execute_forward_2_unit s i forward)

#print axioms issued_forward_2_equals_writeback
#print axioms issue_register_1_not_busy
#print axioms issue_register_2_not_busy
end NutShellProofs
