import Proofs.PipelineCapture
set_option linter.unusedSimpArgs false
namespace NutShellProofs
open nNutCore
theorem writeback_select_0 (s : State) (i : Inputs)
    (unit : v11820 s i = BitVec.ofNat 3 0) :
    v11842 s i = v11835 s i := by
  simp [v4, v11821, v11823, v11824, v11826, v11827, v11829, v11830, v11832, v11833, v110, v11834, v11836, v11837, v11838, v11839, v11840, v11841, v11842, unit]
theorem writeback_capture_0 (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1)
    (unit : v3 s i = BitVec.ofNat 3 0) :
    v11842 (step s i) next = v25535 s i := by
  have selected : v11820 (step s i) next = BitVec.ofNat 3 0 := by
    change (step s i).g50.r1609_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fctrl_5FfuType = _
    rw [capture_decode_ctrl_fuType s i next commit]
    exact unit
  rw [writeback_select_0 _ _ selected]
  exact capture_commits_0 s i next commit
theorem writeback_select_1 (s : State) (i : Inputs)
    (unit : v11820 s i = BitVec.ofNat 3 1) :
    v11842 s i = v11831 s i := by
  simp [v4, v11821, v11823, v11824, v11826, v11827, v11829, v11830, v11832, v11833, v110, v11834, v11836, v11837, v11838, v11839, v11840, v11841, v11842, unit]
theorem writeback_capture_1 (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1)
    (unit : v3 s i = BitVec.ofNat 3 1) :
    v11842 (step s i) next = v25537 s i := by
  have selected : v11820 (step s i) next = BitVec.ofNat 3 1 := by
    change (step s i).g50.r1609_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fctrl_5FfuType = _
    rw [capture_decode_ctrl_fuType s i next commit]
    exact unit
  rw [writeback_select_1 _ _ selected]
  exact capture_commits_1 s i next commit
theorem writeback_select_2 (s : State) (i : Inputs)
    (unit : v11820 s i = BitVec.ofNat 3 2) :
    v11842 s i = v11828 s i := by
  simp [v4, v11821, v11823, v11824, v11826, v11827, v11829, v11830, v11832, v11833, v110, v11834, v11836, v11837, v11838, v11839, v11840, v11841, v11842, unit]
theorem writeback_capture_2 (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1)
    (unit : v3 s i = BitVec.ofNat 3 2) :
    v11842 (step s i) next = v25569 s i := by
  have selected : v11820 (step s i) next = BitVec.ofNat 3 2 := by
    change (step s i).g50.r1609_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fctrl_5FfuType = _
    rw [capture_decode_ctrl_fuType s i next commit]
    exact unit
  rw [writeback_select_2 _ _ selected]
  exact capture_commits_2 s i next commit
theorem writeback_select_3 (s : State) (i : Inputs)
    (unit : v11820 s i = BitVec.ofNat 3 3) :
    v11842 s i = v11825 s i := by
  simp [v4, v11821, v11823, v11824, v11826, v11827, v11829, v11830, v11832, v11833, v110, v11834, v11836, v11837, v11838, v11839, v11840, v11841, v11842, unit]
theorem writeback_capture_3 (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1)
    (unit : v3 s i = BitVec.ofNat 3 3) :
    v11842 (step s i) next = v25572 s i := by
  have selected : v11820 (step s i) next = BitVec.ofNat 3 3 := by
    change (step s i).g50.r1609_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fctrl_5FfuType = _
    rw [capture_decode_ctrl_fuType s i next commit]
    exact unit
  rw [writeback_select_3 _ _ selected]
  exact capture_commits_3 s i next commit
theorem writeback_select_4 (s : State) (i : Inputs)
    (unit : v11820 s i = BitVec.ofNat 3 4) :
    v11842 s i = v11822 s i := by
  simp [v4, v11821, v11823, v11824, v11826, v11827, v11829, v11830, v11832, v11833, v110, v11834, v11836, v11837, v11838, v11839, v11840, v11841, v11842, unit]
theorem writeback_capture_4 (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1)
    (unit : v3 s i = BitVec.ofNat 3 4) :
    v11842 (step s i) next = v25574 s i := by
  have selected : v11820 (step s i) next = BitVec.ofNat 3 4 := by
    change (step s i).g50.r1609_nbackend_5Fwbu_5Fio_5Fin_5Fbits_5Fr_5Fdecode_5Fctrl_5FfuType = _
    rw [capture_decode_ctrl_fuType s i next commit]
    exact unit
  rw [writeback_select_4 _ _ selected]
  exact capture_commits_4 s i next commit
#print axioms writeback_capture_0
#print axioms writeback_capture_1
end NutShellProofs
