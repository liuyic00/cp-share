import Proofs.RegisterFrame
import Proofs.DestinationAlignment
import Proofs.DecodeCases
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedSimpArgs false
theorem registers_agree_no_writes (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (reset : i.nreset = 0)
    (write : v704 s i = 0) (destination : v1320 s i = 0) :
    RegisterAgreement (step s i) := by
  constructor
  · have other : v1320 s i ≠ 1#5 := by simp [destination]
    have ref := reference_frame_x1 s i reset other
    have dut := dut_read_after_step s i reset 1#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x1.trans ref.symm)
  · have other : v1320 s i ≠ 2#5 := by simp [destination]
    have ref := reference_frame_x2 s i reset other
    have dut := dut_read_after_step s i reset 2#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x2.trans ref.symm)
  · have other : v1320 s i ≠ 3#5 := by simp [destination]
    have ref := reference_frame_x3 s i reset other
    have dut := dut_read_after_step s i reset 3#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x3.trans ref.symm)
  · have other : v1320 s i ≠ 4#5 := by simp [destination]
    have ref := reference_frame_x4 s i reset other
    have dut := dut_read_after_step s i reset 4#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x4.trans ref.symm)
  · have other : v1320 s i ≠ 5#5 := by simp [destination]
    have ref := reference_frame_x5 s i reset other
    have dut := dut_read_after_step s i reset 5#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x5.trans ref.symm)
  · have other : v1320 s i ≠ 6#5 := by simp [destination]
    have ref := reference_frame_x6 s i reset other
    have dut := dut_read_after_step s i reset 6#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x6.trans ref.symm)
  · have other : v1320 s i ≠ 7#5 := by simp [destination]
    have ref := reference_frame_x7 s i reset other
    have dut := dut_read_after_step s i reset 7#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x7.trans ref.symm)
  · have other : v1320 s i ≠ 8#5 := by simp [destination]
    have ref := reference_frame_x8 s i reset other
    have dut := dut_read_after_step s i reset 8#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x8.trans ref.symm)
  · have other : v1320 s i ≠ 9#5 := by simp [destination]
    have ref := reference_frame_x9 s i reset other
    have dut := dut_read_after_step s i reset 9#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x9.trans ref.symm)
  · have other : v1320 s i ≠ 10#5 := by simp [destination]
    have ref := reference_frame_x10 s i reset other
    have dut := dut_read_after_step s i reset 10#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x10.trans ref.symm)
  · have other : v1320 s i ≠ 11#5 := by simp [destination]
    have ref := reference_frame_x11 s i reset other
    have dut := dut_read_after_step s i reset 11#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x11.trans ref.symm)
  · have other : v1320 s i ≠ 12#5 := by simp [destination]
    have ref := reference_frame_x12 s i reset other
    have dut := dut_read_after_step s i reset 12#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x12.trans ref.symm)
  · have other : v1320 s i ≠ 13#5 := by simp [destination]
    have ref := reference_frame_x13 s i reset other
    have dut := dut_read_after_step s i reset 13#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x13.trans ref.symm)
  · have other : v1320 s i ≠ 14#5 := by simp [destination]
    have ref := reference_frame_x14 s i reset other
    have dut := dut_read_after_step s i reset 14#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x14.trans ref.symm)
  · have other : v1320 s i ≠ 15#5 := by simp [destination]
    have ref := reference_frame_x15 s i reset other
    have dut := dut_read_after_step s i reset 15#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x15.trans ref.symm)
  · have other : v1320 s i ≠ 16#5 := by simp [destination]
    have ref := reference_frame_x16 s i reset other
    have dut := dut_read_after_step s i reset 16#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x16.trans ref.symm)
  · have other : v1320 s i ≠ 17#5 := by simp [destination]
    have ref := reference_frame_x17 s i reset other
    have dut := dut_read_after_step s i reset 17#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x17.trans ref.symm)
  · have other : v1320 s i ≠ 18#5 := by simp [destination]
    have ref := reference_frame_x18 s i reset other
    have dut := dut_read_after_step s i reset 18#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x18.trans ref.symm)
  · have other : v1320 s i ≠ 19#5 := by simp [destination]
    have ref := reference_frame_x19 s i reset other
    have dut := dut_read_after_step s i reset 19#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x19.trans ref.symm)
  · have other : v1320 s i ≠ 20#5 := by simp [destination]
    have ref := reference_frame_x20 s i reset other
    have dut := dut_read_after_step s i reset 20#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x20.trans ref.symm)
  · have other : v1320 s i ≠ 21#5 := by simp [destination]
    have ref := reference_frame_x21 s i reset other
    have dut := dut_read_after_step s i reset 21#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x21.trans ref.symm)
  · have other : v1320 s i ≠ 22#5 := by simp [destination]
    have ref := reference_frame_x22 s i reset other
    have dut := dut_read_after_step s i reset 22#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x22.trans ref.symm)
  · have other : v1320 s i ≠ 23#5 := by simp [destination]
    have ref := reference_frame_x23 s i reset other
    have dut := dut_read_after_step s i reset 23#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x23.trans ref.symm)
  · have other : v1320 s i ≠ 24#5 := by simp [destination]
    have ref := reference_frame_x24 s i reset other
    have dut := dut_read_after_step s i reset 24#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x24.trans ref.symm)
  · have other : v1320 s i ≠ 25#5 := by simp [destination]
    have ref := reference_frame_x25 s i reset other
    have dut := dut_read_after_step s i reset 25#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x25.trans ref.symm)
  · have other : v1320 s i ≠ 26#5 := by simp [destination]
    have ref := reference_frame_x26 s i reset other
    have dut := dut_read_after_step s i reset 26#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x26.trans ref.symm)
  · have other : v1320 s i ≠ 27#5 := by simp [destination]
    have ref := reference_frame_x27 s i reset other
    have dut := dut_read_after_step s i reset 27#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x27.trans ref.symm)
  · have other : v1320 s i ≠ 28#5 := by simp [destination]
    have ref := reference_frame_x28 s i reset other
    have dut := dut_read_after_step s i reset 28#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x28.trans ref.symm)
  · have other : v1320 s i ≠ 29#5 := by simp [destination]
    have ref := reference_frame_x29 s i reset other
    have dut := dut_read_after_step s i reset 29#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x29.trans ref.symm)
  · have other : v1320 s i ≠ 30#5 := by simp [destination]
    have ref := reference_frame_x30 s i reset other
    have dut := dut_read_after_step s i reset 30#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x30.trans ref.symm)
  · have other : v1320 s i ≠ 31#5 := by simp [destination]
    have ref := reference_frame_x31 s i reset other
    have dut := dut_read_after_step s i reset 31#5
    simp [write, dutRead] at dut
    exact dut.trans (agree.x31.trans ref.symm)
theorem register_tasks_no_writes (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (reset : i.nreset = 0) (commit : v964 s i = 1)
    (write : v704 s i = 0) (destination : v1320 s i = 0) : RegisterTasks s i :=
  (register_tasks_iff_next s i reset commit).mpr
    (registers_agree_no_writes s i agree reset write destination)
private theorem no_write_branch_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem no_write_branch_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem no_write_branch_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1122 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1122 s i = 0 := by
  change (if (1073762355 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1130 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1130 s i = 0 := by
  change (if (1073741875 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1138 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1138 s i = 0 := by
  change (if (20531 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1146 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1146 s i = 0 := by
  change (if (4147 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1154 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1154 s i = 0 := by
  change (if (16435 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1162 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1162 s i = 0 := by
  change (if (24627 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 4261441663 24627 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1170 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1170 s i = 0 := by
  change (if (28723 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 4261441663 28723 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1178 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1178 s i = 0 := by
  change (if (12339 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1186 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1186 s i = 0 := by
  change (if (8243 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1194 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1194 s i = 0 := by
  change (if (51 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1203 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1203 s i = 0 := by
  change (if (23 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1209 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1209 s i = 0 := by
  change (if (55 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1214 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1214 s i = 0 := by
  change (if (1073762323 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1221 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1221 s i = 0 := by
  change (if (20499 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1228 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1228 s i = 0 := by
  change (if (4115 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1236 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1236 s i = 0 := by
  change (if (16403 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1244 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1244 s i = 0 := by
  change (if (24595 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1252 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1252 s i = 0 := by
  change (if (28691 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1260 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1260 s i = 0 := by
  change (if (12307 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1268 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1268 s i = 0 := by
  change (if (8211 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_branch_v1276 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1276 s i = 0 := by
  change (if (19 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 99 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_branch_no_destination (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99) : v1320 s i = 0 := by
  simp [v1320, commit, v150, v1319, v1318, v1317, v1316, v1315, v1314, v1313, v1312, v1311, v1310, v1309, v1308, v1307, v1306, v1305, v1304, v1303, v1302, v1301, v1300, v1299, v1298, v1297, v1296, v1295, v1294, v1293, v1292, v1291, v1290, v1289, v1288, v1287, v1286, v1285, v1284, v1283, v1282, v1281, no_write_branch_v980 s i commit known, no_write_branch_v989 s i commit known, no_write_branch_v997 s i commit known, no_write_branch_v1005 s i commit known, no_write_branch_v1013 s i commit known, no_write_branch_v1021 s i commit known, no_write_branch_v1029 s i commit known, no_write_branch_v1037 s i commit known, no_write_branch_v1046 s i commit known, no_write_branch_v1052 s i commit known, no_write_branch_v1058 s i commit known, no_write_branch_v1066 s i commit known, no_write_branch_v1074 s i commit known, no_write_branch_v1082 s i commit known, no_write_branch_v1090 s i commit known, no_write_branch_v1098 s i commit known, no_write_branch_v1106 s i commit known, no_write_branch_v1114 s i commit known, no_write_branch_v1122 s i commit known, no_write_branch_v1130 s i commit known, no_write_branch_v1138 s i commit known, no_write_branch_v1146 s i commit known, no_write_branch_v1154 s i commit known, no_write_branch_v1162 s i commit known, no_write_branch_v1170 s i commit known, no_write_branch_v1178 s i commit known, no_write_branch_v1186 s i commit known, no_write_branch_v1194 s i commit known, no_write_branch_v1203 s i commit known, no_write_branch_v1209 s i commit known, no_write_branch_v1214 s i commit known, no_write_branch_v1221 s i commit known, no_write_branch_v1228 s i commit known, no_write_branch_v1236 s i commit known, no_write_branch_v1244 s i commit known, no_write_branch_v1252 s i commit known, no_write_branch_v1260 s i commit known, no_write_branch_v1268 s i commit known, no_write_branch_v1276 s i commit known]
private theorem no_write_store_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem no_write_store_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem no_write_store_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1122 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1122 s i = 0 := by
  change (if (1073762355 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1130 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1130 s i = 0 := by
  change (if (1073741875 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1138 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1138 s i = 0 := by
  change (if (20531 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1146 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1146 s i = 0 := by
  change (if (4147 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1154 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1154 s i = 0 := by
  change (if (16435 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1162 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1162 s i = 0 := by
  change (if (24627 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 4261441663 24627 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1170 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1170 s i = 0 := by
  change (if (28723 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 4261441663 28723 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1178 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1178 s i = 0 := by
  change (if (12339 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1186 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1186 s i = 0 := by
  change (if (8243 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1194 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1194 s i = 0 := by
  change (if (51 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1203 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1203 s i = 0 := by
  change (if (23 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1209 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1209 s i = 0 := by
  change (if (55 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1214 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1214 s i = 0 := by
  change (if (1073762323 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1221 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1221 s i = 0 := by
  change (if (20499 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1228 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1228 s i = 0 := by
  change (if (4115 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1236 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1236 s i = 0 := by
  change (if (16403 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1244 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1244 s i = 0 := by
  change (if (24595 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1252 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1252 s i = 0 := by
  change (if (28691 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1260 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1260 s i = 0 := by
  change (if (12307 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1268 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1268 s i = 0 := by
  change (if (8211 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem no_write_store_v1276 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1276 s i = 0 := by
  change (if (19 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  simp only [v977, v975, v974, v973, commit, if_true]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 35 28799 19 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_store_no_destination (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35) : v1320 s i = 0 := by
  simp [v1320, commit, v150, v1319, v1318, v1317, v1316, v1315, v1314, v1313, v1312, v1311, v1310, v1309, v1308, v1307, v1306, v1305, v1304, v1303, v1302, v1301, v1300, v1299, v1298, v1297, v1296, v1295, v1294, v1293, v1292, v1291, v1290, v1289, v1288, v1287, v1286, v1285, v1284, v1283, v1282, v1281, no_write_store_v980 s i commit known, no_write_store_v989 s i commit known, no_write_store_v997 s i commit known, no_write_store_v1005 s i commit known, no_write_store_v1013 s i commit known, no_write_store_v1021 s i commit known, no_write_store_v1029 s i commit known, no_write_store_v1037 s i commit known, no_write_store_v1046 s i commit known, no_write_store_v1052 s i commit known, no_write_store_v1058 s i commit known, no_write_store_v1066 s i commit known, no_write_store_v1074 s i commit known, no_write_store_v1082 s i commit known, no_write_store_v1090 s i commit known, no_write_store_v1098 s i commit known, no_write_store_v1106 s i commit known, no_write_store_v1114 s i commit known, no_write_store_v1122 s i commit known, no_write_store_v1130 s i commit known, no_write_store_v1138 s i commit known, no_write_store_v1146 s i commit known, no_write_store_v1154 s i commit known, no_write_store_v1162 s i commit known, no_write_store_v1170 s i commit known, no_write_store_v1178 s i commit known, no_write_store_v1186 s i commit known, no_write_store_v1194 s i commit known, no_write_store_v1203 s i commit known, no_write_store_v1209 s i commit known, no_write_store_v1214 s i commit known, no_write_store_v1221 s i commit known, no_write_store_v1228 s i commit known, no_write_store_v1236 s i commit known, no_write_store_v1244 s i commit known, no_write_store_v1252 s i commit known, no_write_store_v1260 s i commit known, no_write_store_v1268 s i commit known, no_write_store_v1276 s i commit known]
theorem register_tasks_beq_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : RegisterTasks s i := by
  have ctrl := control_values_at_commit s i control reset commit
  have disabled := ctrl.write_enable.trans (beq_write_enable _ known)
  have write : v704 s i = 0 := by simp [v704, v700, v699, v697, disabled]
  have opcode : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 127 known (by decide)
  exact register_tasks_no_writes s i agree reset commit write
    (reference_branch_no_destination s i commit opcode)
#print axioms register_tasks_beq_commit
theorem register_tasks_bne_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : RegisterTasks s i := by
  have ctrl := control_values_at_commit s i control reset commit
  have disabled := ctrl.write_enable.trans (bne_write_enable _ known)
  have write : v704 s i = 0 := by simp [v704, v700, v699, v697, disabled]
  have opcode : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 127 known (by decide)
  exact register_tasks_no_writes s i agree reset commit write
    (reference_branch_no_destination s i commit opcode)
#print axioms register_tasks_bne_commit
theorem register_tasks_blt_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : RegisterTasks s i := by
  have ctrl := control_values_at_commit s i control reset commit
  have disabled := ctrl.write_enable.trans (blt_write_enable _ known)
  have write : v704 s i = 0 := by simp [v704, v700, v699, v697, disabled]
  have opcode : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 127 known (by decide)
  exact register_tasks_no_writes s i agree reset commit write
    (reference_branch_no_destination s i commit opcode)
#print axioms register_tasks_blt_commit
theorem register_tasks_bge_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : RegisterTasks s i := by
  have ctrl := control_values_at_commit s i control reset commit
  have disabled := ctrl.write_enable.trans (bge_write_enable _ known)
  have write : v704 s i = 0 := by simp [v704, v700, v699, v697, disabled]
  have opcode : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 127 known (by decide)
  exact register_tasks_no_writes s i agree reset commit write
    (reference_branch_no_destination s i commit opcode)
#print axioms register_tasks_bge_commit
theorem register_tasks_bltu_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : RegisterTasks s i := by
  have ctrl := control_values_at_commit s i control reset commit
  have disabled := ctrl.write_enable.trans (bltu_write_enable _ known)
  have write : v704 s i = 0 := by simp [v704, v700, v699, v697, disabled]
  have opcode : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 127 known (by decide)
  exact register_tasks_no_writes s i agree reset commit write
    (reference_branch_no_destination s i commit opcode)
#print axioms register_tasks_bltu_commit
theorem register_tasks_bgeu_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : RegisterTasks s i := by
  have ctrl := control_values_at_commit s i control reset commit
  have disabled := ctrl.write_enable.trans (bgeu_write_enable _ known)
  have write : v704 s i = 0 := by simp [v704, v700, v699, v697, disabled]
  have opcode : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 99 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 127 known (by decide)
  exact register_tasks_no_writes s i agree reset commit write
    (reference_branch_no_destination s i commit opcode)
#print axioms register_tasks_bgeu_commit
theorem register_tasks_sb_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : RegisterTasks s i := by
  have ctrl := control_values_at_commit s i control reset commit
  have disabled := ctrl.write_enable.trans (sb_write_enable _ known)
  have write : v704 s i = 0 := by simp [v704, v700, v699, v697, disabled]
  have opcode : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 127 known (by decide)
  exact register_tasks_no_writes s i agree reset commit write
    (reference_store_no_destination s i commit opcode)
#print axioms register_tasks_sb_commit
theorem register_tasks_sh_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : RegisterTasks s i := by
  have ctrl := control_values_at_commit s i control reset commit
  have disabled := ctrl.write_enable.trans (sh_write_enable _ known)
  have write : v704 s i = 0 := by simp [v704, v700, v699, v697, disabled]
  have opcode : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 127 known (by decide)
  exact register_tasks_no_writes s i agree reset commit write
    (reference_store_no_destination s i commit opcode)
#print axioms register_tasks_sh_commit
theorem register_tasks_sw_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (control : ControlAligned s)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : RegisterTasks s i := by
  have ctrl := control_values_at_commit s i control reset commit
  have disabled := ctrl.write_enable.trans (sw_write_enable _ known)
  have write : v704 s i = 0 := by simp [v704, v700, v699, v697, disabled]
  have opcode : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 35 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 127 known (by decide)
  exact register_tasks_no_writes s i agree reset commit write
    (reference_store_no_destination s i commit opcode)
#print axioms register_tasks_sw_commit
theorem register_tasks_fence_commit (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (_control : ControlAligned s)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4027580415 = 15) : RegisterTasks s i := by
  have h := congrArg (BitVec.extractLsb' 7 5) known
  simp only [BitVec.extractLsb'_and] at h
  have destination : v701 s i = 0 := by
    change (v701 s i &&& BitVec.allOnes 5) = 0 at h
    exact (BitVec.and_allOnes (x := v701 s i)).symm.trans h
  exact register_tasks_rd_zero s i agree reset commit destination
#print axioms register_tasks_fence_commit
def NonwritingInstruction (instruction : BitVec 32) : Prop :=
  instruction &&& 28799 = 99 ∨
  instruction &&& 28799 = 4195 ∨
  instruction &&& 28799 = 16483 ∨
  instruction &&& 28799 = 20579 ∨
  instruction &&& 28799 = 24675 ∨
  instruction &&& 28799 = 28771 ∨
  instruction &&& 28799 = 35 ∨
  instruction &&& 28799 = 4131 ∨
  instruction &&& 28799 = 8227 ∨
  instruction &&& 4027580415 = 15
theorem nonwriting_tasks_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (commit : v964 (run initial inputs t) (inputs t) = 1)
    (instruction : NonwritingInstruction
      (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) :
    RegisterTasks (run initial inputs t) (inputs t) := by
  have control := control_alignment_reachable initial inputs cycles reset env t ht
  rcases instruction with known | known | known | known | known | known | known | known | known | known
  · exact register_tasks_beq_commit _ _ agree control (reset.2.2 t ht) commit known
  · exact register_tasks_bne_commit _ _ agree control (reset.2.2 t ht) commit known
  · exact register_tasks_blt_commit _ _ agree control (reset.2.2 t ht) commit known
  · exact register_tasks_bge_commit _ _ agree control (reset.2.2 t ht) commit known
  · exact register_tasks_bltu_commit _ _ agree control (reset.2.2 t ht) commit known
  · exact register_tasks_bgeu_commit _ _ agree control (reset.2.2 t ht) commit known
  · exact register_tasks_sb_commit _ _ agree control (reset.2.2 t ht) commit known
  · exact register_tasks_sh_commit _ _ agree control (reset.2.2 t ht) commit known
  · exact register_tasks_sw_commit _ _ agree control (reset.2.2 t ht) commit known
  · exact register_tasks_fence_commit _ _ agree control (reset.2.2 t ht) commit known
#print axioms nonwriting_tasks_reachable
end RiscvMiniProofs
