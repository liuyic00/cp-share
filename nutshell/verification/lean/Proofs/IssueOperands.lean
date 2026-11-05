import Proofs.IssueHazards
import Proofs.WritebackRead
namespace NutShellProofs
open nNutCore

private theorem and_ones (a b : BitVec 1) (h : a &&& b = 1) : a = 1 ∧ b = 1 := by
  rcases BitVec.eq_zero_or_eq_one a with ha | ha <;>
    rcases BitVec.eq_zero_or_eq_one b with hb | hb <;> simp_all

theorem dut_read_ports_same (s : State) (i : Inputs) (addr : BitVec 5) :
    dutRead2.v25320 s i addr = dutRead.v25201 s i addr := by
  have bound := addr.isLt
  have cases : addr.toNat = 0 ∨ addr.toNat = 1 ∨ addr.toNat = 2 ∨ addr.toNat = 3 ∨ addr.toNat = 4 ∨ addr.toNat = 5 ∨ addr.toNat = 6 ∨ addr.toNat = 7 ∨ addr.toNat = 8 ∨ addr.toNat = 9 ∨ addr.toNat = 10 ∨ addr.toNat = 11 ∨ addr.toNat = 12 ∨ addr.toNat = 13 ∨ addr.toNat = 14 ∨ addr.toNat = 15 ∨ addr.toNat = 16 ∨ addr.toNat = 17 ∨ addr.toNat = 18 ∨ addr.toNat = 19 ∨ addr.toNat = 20 ∨ addr.toNat = 21 ∨ addr.toNat = 22 ∨ addr.toNat = 23 ∨ addr.toNat = 24 ∨ addr.toNat = 25 ∨ addr.toNat = 26 ∨ addr.toNat = 27 ∨ addr.toNat = 28 ∨ addr.toNat = 29 ∨ addr.toNat = 30 ∨ addr.toNat = 31 := by omega
  rcases cases with c0 | c1 | c2 | c3 | c4 | c5 | c6 | c7 | c8 | c9 | c10 | c11 | c12 | c13 | c14 | c15 | c16 | c17 | c18 | c19 | c20 | c21 | c22 | c23 | c24 | c25 | c26 | c27 | c28 | c29 | c30 | c31
  · have eq : addr = (0 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c0)
    rw [eq, dutRead2.read_0, dutRead.read_0]
  · have eq : addr = (1 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c1)
    rw [eq, dutRead2.read_1, dutRead.read_1]
  · have eq : addr = (2 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c2)
    rw [eq, dutRead2.read_2, dutRead.read_2]
  · have eq : addr = (3 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c3)
    rw [eq, dutRead2.read_3, dutRead.read_3]
  · have eq : addr = (4 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c4)
    rw [eq, dutRead2.read_4, dutRead.read_4]
  · have eq : addr = (5 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c5)
    rw [eq, dutRead2.read_5, dutRead.read_5]
  · have eq : addr = (6 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c6)
    rw [eq, dutRead2.read_6, dutRead.read_6]
  · have eq : addr = (7 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c7)
    rw [eq, dutRead2.read_7, dutRead.read_7]
  · have eq : addr = (8 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c8)
    rw [eq, dutRead2.read_8, dutRead.read_8]
  · have eq : addr = (9 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c9)
    rw [eq, dutRead2.read_9, dutRead.read_9]
  · have eq : addr = (10 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c10)
    rw [eq, dutRead2.read_10, dutRead.read_10]
  · have eq : addr = (11 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c11)
    rw [eq, dutRead2.read_11, dutRead.read_11]
  · have eq : addr = (12 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c12)
    rw [eq, dutRead2.read_12, dutRead.read_12]
  · have eq : addr = (13 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c13)
    rw [eq, dutRead2.read_13, dutRead.read_13]
  · have eq : addr = (14 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c14)
    rw [eq, dutRead2.read_14, dutRead.read_14]
  · have eq : addr = (15 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c15)
    rw [eq, dutRead2.read_15, dutRead.read_15]
  · have eq : addr = (16 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c16)
    rw [eq, dutRead2.read_16, dutRead.read_16]
  · have eq : addr = (17 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c17)
    rw [eq, dutRead2.read_17, dutRead.read_17]
  · have eq : addr = (18 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c18)
    rw [eq, dutRead2.read_18, dutRead.read_18]
  · have eq : addr = (19 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c19)
    rw [eq, dutRead2.read_19, dutRead.read_19]
  · have eq : addr = (20 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c20)
    rw [eq, dutRead2.read_20, dutRead.read_20]
  · have eq : addr = (21 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c21)
    rw [eq, dutRead2.read_21, dutRead.read_21]
  · have eq : addr = (22 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c22)
    rw [eq, dutRead2.read_22, dutRead.read_22]
  · have eq : addr = (23 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c23)
    rw [eq, dutRead2.read_23, dutRead.read_23]
  · have eq : addr = (24 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c24)
    rw [eq, dutRead2.read_24, dutRead.read_24]
  · have eq : addr = (25 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c25)
    rw [eq, dutRead2.read_25, dutRead.read_25]
  · have eq : addr = (26 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c26)
    rw [eq, dutRead2.read_26, dutRead.read_26]
  · have eq : addr = (27 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c27)
    rw [eq, dutRead2.read_27, dutRead.read_27]
  · have eq : addr = (28 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c28)
    rw [eq, dutRead2.read_28, dutRead.read_28]
  · have eq : addr = (29 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c29)
    rw [eq, dutRead2.read_29, dutRead.read_29]
  · have eq : addr = (30 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c30)
    rw [eq, dutRead2.read_30, dutRead.read_30]
  · have eq : addr = (31 : BitVec 5) := BitVec.eq_of_toNat_eq (by simpa using c31)
    rw [eq, dutRead2.read_31, dutRead.read_31]
theorem issued_no_execute_dependency_1 (s : State) (i : Inputs)
    (invariant : ExecuteDestinationBusy s) (fire : v24283 s i = 1)
    (noEx : v11741 s i = 0) : v11732 s i = 0 := by
  rcases BitVec.eq_zero_or_eq_one (v11732 s i) with zero | one
  · exact zero
  · have pair := (and_ones _ _ one).1
    have enabled : v11478 s i = 1 := (and_ones _ _ one).2
    have nz : v11729 s i = 1 := (and_ones _ _ pair).1
    have eq : v11730 s i = 1 := (and_ones _ _ pair).2
    have write : v11475 s i = 1 := (and_ones _ _ enabled).1
    have valid : v6 s i = 1 := (and_ones _ _ enabled).2
    have nonzero : v11723 s i ≠ 0 := by simpa [v11729, v11728] using nz
    have same : v11723 s i = v11470 s i := by simpa [v11730] using eq
    have forward := issue_dependency_1_forwards s i invariant fire valid write nonzero same
    rw [noEx] at forward
    contradiction

theorem issued_no_writeback_match_1 (s : State) (i : Inputs)
    (invariant : ExecuteDestinationBusy s) (fire : v24283 s i = 1)
    (noEx : v11741 s i = 0) (noWB : v11750 s i = 0)
    (nonzero : v11723 s i ≠ 0) :
    ¬(v11465 s i = v11723 s i ∧ v11462 s i = 1) := by
  intro ⟨dest, write⟩
  have noDepend := issued_no_execute_dependency_1 s i invariant fire noEx
  have matchWB : v11747 s i = 1 := by
    simp only [v11747, v11746, v11744, v11743, v11745]
    have nz : v11723 s i ≠ BitVec.ofNat 5 0 := nonzero
    rw [if_pos nz, if_pos dest.symm, write]
    rfl
  have allow : v11749 s i = 1 := by
    simp [v11749, v11748, noDepend, v24, v110]
  have forward : v11750 s i = 1 := by
    simp [v11750, matchWB, allow]
  rw [noWB] at forward
  contradiction

theorem issued_plain_register_1 (s : State) (i next : Inputs)
    (invariant : ExecuteDestinationBusy s) (fire : v24283 s i = 1)
    (noEx : v11741 s i = 0) (noWB : v11750 s i = 0)
    (kind : v24881 s i = 0) (reset : i.g0.nreset = 0) :
    (step s i).g48.r1564_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc1 =
      dutRead.v25201 (step s i) next (v11723 s i) := by
  rw [operand_1_capture s i fire, operand_1_register s i kind noEx noWB,
    dutRead.actual]
  rw [dut_read_step s i next _ reset]
  by_cases zero : v11723 s i = 0
  · rw [if_pos zero, zero, dutRead.read_0]
  · rw [if_neg zero, if_neg (issued_no_writeback_match_1 s i invariant fire noEx noWB zero)]

theorem issued_non_execute_operand_1 (s : State) (i next : Inputs)
    (invariant : ExecuteDestinationBusy s) (fire : v24283 s i = 1)
    (noEx : v11741 s i = 0) (kind : v24881 s i = 0)
    (reset : i.g0.nreset = 0) :
    (step s i).g48.r1564_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc1 =
      dutRead.v25201 (step s i) next (v11723 s i) := by
  rcases BitVec.eq_zero_or_eq_one (v11750 s i) with noWB | wb
  · exact issued_plain_register_1 s i next invariant fire noEx noWB kind reset
  · exact captured_writeback_1_equals_register s i next fire noEx wb kind reset

#print axioms issued_non_execute_operand_1
theorem issued_no_execute_dependency_2 (s : State) (i : Inputs)
    (invariant : ExecuteDestinationBusy s) (fire : v24283 s i = 1)
    (noEx : v11776 s i = 0) : v11774 s i = 0 := by
  rcases BitVec.eq_zero_or_eq_one (v11774 s i) with zero | one
  · exact zero
  · have pair := (and_ones _ _ one).1
    have enabled : v11478 s i = 1 := (and_ones _ _ one).2
    have nz : v11771 s i = 1 := (and_ones _ _ pair).1
    have eq : v11772 s i = 1 := (and_ones _ _ pair).2
    have write : v11475 s i = 1 := (and_ones _ _ enabled).1
    have valid : v6 s i = 1 := (and_ones _ _ enabled).2
    have nonzero : v11765 s i ≠ 0 := by simpa [v11771, v11770] using nz
    have same : v11765 s i = v11470 s i := by simpa [v11772] using eq
    have forward := issue_dependency_2_forwards s i invariant fire valid write nonzero same
    rw [noEx] at forward
    contradiction

theorem issued_no_writeback_match_2 (s : State) (i : Inputs)
    (invariant : ExecuteDestinationBusy s) (fire : v24283 s i = 1)
    (noEx : v11776 s i = 0) (noWB : v11785 s i = 0)
    (nonzero : v11765 s i ≠ 0) :
    ¬(v11465 s i = v11765 s i ∧ v11462 s i = 1) := by
  intro ⟨dest, write⟩
  have noDepend := issued_no_execute_dependency_2 s i invariant fire noEx
  have matchWB : v11782 s i = 1 := by
    simp only [v11782, v11781, v11779, v11778, v11780]
    have nz : v11765 s i ≠ BitVec.ofNat 5 0 := nonzero
    rw [if_pos nz, if_pos dest.symm, write]
    rfl
  have allow : v11784 s i = 1 := by
    simp [v11784, v11783, noDepend, v24, v110]
  have forward : v11785 s i = 1 := by
    simp [v11785, matchWB, allow]
  rw [noWB] at forward
  contradiction

theorem issued_plain_register_2 (s : State) (i next : Inputs)
    (invariant : ExecuteDestinationBusy s) (fire : v24283 s i = 1)
    (noEx : v11776 s i = 0) (noWB : v11785 s i = 0)
    (kind : v24896 s i = 0) (reset : i.g0.nreset = 0) :
    (step s i).g48.r1565_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc2 =
      dutRead.v25201 (step s i) next (v11765 s i) := by
  rw [operand_2_capture s i fire, operand_2_register s i kind noEx noWB,
    dutRead2.actual]
  rw [dut_read_ports_same]
  rw [dut_read_step s i next _ reset]
  by_cases zero : v11765 s i = 0
  · rw [if_pos zero, zero, dutRead.read_0]
  · rw [if_neg zero, if_neg (issued_no_writeback_match_2 s i invariant fire noEx noWB zero)]

theorem issued_non_execute_operand_2 (s : State) (i next : Inputs)
    (invariant : ExecuteDestinationBusy s) (fire : v24283 s i = 1)
    (noEx : v11776 s i = 0) (kind : v24896 s i = 0)
    (reset : i.g0.nreset = 0) :
    (step s i).g48.r1565_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc2 =
      dutRead.v25201 (step s i) next (v11765 s i) := by
  rcases BitVec.eq_zero_or_eq_one (v11785 s i) with noWB | wb
  · exact issued_plain_register_2 s i next invariant fire noEx noWB kind reset
  · exact captured_writeback_2_equals_register s i next fire noEx wb kind reset

#print axioms issued_non_execute_operand_2
end NutShellProofs
