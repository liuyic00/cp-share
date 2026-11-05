import Proofs.ScoreboardInvariant
namespace NutShellProofs
open nNutCore

private theorem query_bit (busy : BitVec 32) (addr : BitVec 5) :
    (BitVec.extractLsb' 0 1 (BitVec.ushiftRight busy
      (((0 : BitVec 27) ++ addr).toNat))).getLsbD 0 = busy.getLsbD addr.toNat := by
  have cast : ((0 : BitVec 27) ++ addr).toNat = addr.toNat := by
    rw [BitVec.toNat_append]
    simp
  rw [cast, BitVec.getLsbD_extractLsb', BitVec.ushiftRight_eq, BitVec.getLsbD_ushiftRight]
  simp

theorem issue_dependency_1_forwards (s : State) (i : Inputs)
    (invariant : ExecuteDestinationBusy s) (fire : v24283 s i = 1)
    (valid : v6 s i = 1) (write : v11475 s i = 1)
    (nonzero : v11723 s i ≠ 0) (same : v11723 s i = v11470 s i) :
    v11741 s i = 1 := by
  have validWrite : v11478 s i = 1 := by
    simp [v11478, v11477, v11476, valid, write]
  have matched : v11732 s i = 1 := by
    simp only [v11732, v11731, v11729, v11728, v11730]
    have nz : v11723 s i ≠ BitVec.ofNat 5 0 := nonzero
    rw [if_pos nz, if_pos same, validWrite]
    rfl
  have busy : s.g40.r1285_nbackend_5Fisu_5Fbusy.getLsbD (v11723 s i).toNat = true := by
    rw [same]
    exact invariant valid write (fun h => nonzero (same.trans h))
  have query : (v11726 s i).getLsbD 0 = true := by
    have bridge := query_bit s.g40.r1285_nbackend_5Fisu_5Fbusy (v11723 s i)
    exact bridge.trans busy
  rcases BitVec.eq_zero_or_eq_one (v11739 s i) with allowed | blocked
  · simp [v11741, matched, v11740, allowed, v24]
  · have noEx : v11741 s i = 0 := by
      simp [v11741, matched, v11740, blocked, v24]
    have noWB : v11750 s i = 0 := by
      simp [v11750, v11749, blocked, v11748, matched, v24]
    have free := issue_register_1_not_busy s i fire noEx noWB
    simp [free] at query

#print axioms issue_dependency_1_forwards

theorem issue_dependency_2_forwards (s : State) (i : Inputs)
    (invariant : ExecuteDestinationBusy s) (fire : v24283 s i = 1)
    (valid : v6 s i = 1) (write : v11475 s i = 1)
    (nonzero : v11765 s i ≠ 0) (same : v11765 s i = v11470 s i) :
    v11776 s i = 1 := by
  have validWrite : v11478 s i = 1 := by
    simp [v11478, v11477, v11476, valid, write]
  have matched : v11774 s i = 1 := by
    simp only [v11774, v11773, v11771, v11770, v11772]
    have nz : v11765 s i ≠ BitVec.ofNat 5 0 := nonzero
    rw [if_pos nz, if_pos same, validWrite]
    rfl
  have busy : s.g40.r1285_nbackend_5Fisu_5Fbusy.getLsbD (v11765 s i).toNat = true := by
    rw [same]
    exact invariant valid write (fun h => nonzero (same.trans h))
  have query : (v11768 s i).getLsbD 0 = true := by
    have bridge := query_bit s.g40.r1285_nbackend_5Fisu_5Fbusy (v11765 s i)
    exact bridge.trans busy
  rcases BitVec.eq_zero_or_eq_one (v11739 s i) with allowed | blocked
  · simp [v11776, matched, v11775, allowed, v24]
  · have noEx : v11776 s i = 0 := by
      simp [v11776, matched, v11775, blocked, v24]
    have noWB : v11785 s i = 0 := by
      simp [v11785, v11784, blocked, v11783, matched, v24]
    have free := issue_register_2_not_busy s i fire noEx noWB
    simp [free] at query

#print axioms issue_dependency_2_forwards
theorem issued_dependency_1_value (s : State) (i next : Inputs)
    (invariant : ExecuteDestinationBusy s) (fire : v24283 s i = 1)
    (valid : v6 s i = 1) (write : v11475 s i = 1)
    (nonzero : v11723 s i ≠ 0) (same : v11723 s i = v11470 s i)
    (kind : v24881 s i = 0) (reset : i.g0.nreset = 0) (flush : v23 s i = 0) :
    (step s i).g48.r1564_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc1 =
      v11842 (step s i) next := by
  exact issued_forward_1_equals_writeback s i next fire
    (issue_dependency_1_forwards s i invariant fire valid write nonzero same)
    kind reset flush

#print axioms issued_dependency_1_value
theorem issued_dependency_2_value (s : State) (i next : Inputs)
    (invariant : ExecuteDestinationBusy s) (fire : v24283 s i = 1)
    (valid : v6 s i = 1) (write : v11475 s i = 1)
    (nonzero : v11765 s i ≠ 0) (same : v11765 s i = v11470 s i)
    (kind : v24896 s i = 0) (reset : i.g0.nreset = 0) (flush : v23 s i = 0) :
    (step s i).g48.r1565_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fsrc2 =
      v11842 (step s i) next := by
  exact issued_forward_2_equals_writeback s i next fire
    (issue_dependency_2_forwards s i invariant fire valid write nonzero same)
    kind reset flush

#print axioms issued_dependency_2_value
end NutShellProofs
