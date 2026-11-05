import Proofs.RegisterRelation
namespace RiscvMiniProofs
open nCoreSoc
-- These equivalences do not prove their right-hand sides. They tie each
-- original generated task to the actual next-state relation.
theorem register_task_1_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨9, by decide⟩ s i ↔
      (step s i).g0.r22_ndut_5Fdpath_5FregFile_5Fregs_5F1 = (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9293 s i ≠ 1 ∨ v9291 s i = 1) = true) ↔ (v774 s i) = (v2431 s i)
  simp [v0, v1, v4, v694, v770, v771, v772, v773, v774, v955, v956, v2431, v9284, v9285, v9286, v9287, v9288, v9289, v9290, v9291, v9292, v9293, reset, committed]

theorem register_task_2_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨10, by decide⟩ s i ↔
      (step s i).g0.r23_ndut_5Fdpath_5FregFile_5Fregs_5F2 = (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9303 s i ≠ 1 ∨ v9301 s i = 1) = true) ↔ (v780 s i) = (v2585 s i)
  simp [v0, v1, v4, v694, v776, v777, v778, v779, v780, v955, v956, v2585, v9294, v9295, v9296, v9297, v9298, v9299, v9300, v9301, v9302, v9303, reset, committed]

theorem register_task_3_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨11, by decide⟩ s i ↔
      (step s i).g0.r24_ndut_5Fdpath_5FregFile_5Fregs_5F3 = (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9313 s i ≠ 1 ∨ v9311 s i = 1) = true) ↔ (v786 s i) = (v2739 s i)
  simp [v0, v1, v4, v694, v782, v783, v784, v785, v786, v955, v956, v2739, v9304, v9305, v9306, v9307, v9308, v9309, v9310, v9311, v9312, v9313, reset, committed]

theorem register_task_4_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨12, by decide⟩ s i ↔
      (step s i).g0.r25_ndut_5Fdpath_5FregFile_5Fregs_5F4 = (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9323 s i ≠ 1 ∨ v9321 s i = 1) = true) ↔ (v792 s i) = (v2893 s i)
  simp [v0, v1, v4, v694, v788, v789, v790, v791, v792, v955, v956, v2893, v9314, v9315, v9316, v9317, v9318, v9319, v9320, v9321, v9322, v9323, reset, committed]

theorem register_task_5_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨13, by decide⟩ s i ↔
      (step s i).g0.r26_ndut_5Fdpath_5FregFile_5Fregs_5F5 = (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9333 s i ≠ 1 ∨ v9331 s i = 1) = true) ↔ (v798 s i) = (v3047 s i)
  simp [v0, v1, v4, v694, v794, v795, v796, v797, v798, v955, v956, v3047, v9324, v9325, v9326, v9327, v9328, v9329, v9330, v9331, v9332, v9333, reset, committed]

theorem register_task_6_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨14, by decide⟩ s i ↔
      (step s i).g0.r27_ndut_5Fdpath_5FregFile_5Fregs_5F6 = (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9343 s i ≠ 1 ∨ v9341 s i = 1) = true) ↔ (v804 s i) = (v3201 s i)
  simp [v0, v1, v4, v694, v800, v801, v802, v803, v804, v955, v956, v3201, v9334, v9335, v9336, v9337, v9338, v9339, v9340, v9341, v9342, v9343, reset, committed]

theorem register_task_7_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨15, by decide⟩ s i ↔
      (step s i).g0.r28_ndut_5Fdpath_5FregFile_5Fregs_5F7 = (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9353 s i ≠ 1 ∨ v9351 s i = 1) = true) ↔ (v810 s i) = (v3355 s i)
  simp [v0, v1, v4, v694, v806, v807, v808, v809, v810, v955, v956, v3355, v9344, v9345, v9346, v9347, v9348, v9349, v9350, v9351, v9352, v9353, reset, committed]

theorem register_task_8_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨16, by decide⟩ s i ↔
      (step s i).g0.r29_ndut_5Fdpath_5FregFile_5Fregs_5F8 = (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9363 s i ≠ 1 ∨ v9361 s i = 1) = true) ↔ (v816 s i) = (v3509 s i)
  simp [v0, v1, v4, v694, v812, v813, v814, v815, v816, v955, v956, v3509, v9354, v9355, v9356, v9357, v9358, v9359, v9360, v9361, v9362, v9363, reset, committed]

theorem register_task_9_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨17, by decide⟩ s i ↔
      (step s i).g0.r30_ndut_5Fdpath_5FregFile_5Fregs_5F9 = (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9373 s i ≠ 1 ∨ v9371 s i = 1) = true) ↔ (v822 s i) = (v3663 s i)
  simp [v0, v1, v4, v694, v818, v819, v820, v821, v822, v955, v956, v3663, v9364, v9365, v9366, v9367, v9368, v9369, v9370, v9371, v9372, v9373, reset, committed]

theorem register_task_10_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨18, by decide⟩ s i ↔
      (step s i).g0.r31_ndut_5Fdpath_5FregFile_5Fregs_5F10 = (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9383 s i ≠ 1 ∨ v9381 s i = 1) = true) ↔ (v828 s i) = (v3817 s i)
  simp [v0, v1, v4, v694, v824, v825, v826, v827, v828, v955, v956, v3817, v9374, v9375, v9376, v9377, v9378, v9379, v9380, v9381, v9382, v9383, reset, committed]

theorem register_task_11_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨19, by decide⟩ s i ↔
      (step s i).g1.r32_ndut_5Fdpath_5FregFile_5Fregs_5F11 = (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9393 s i ≠ 1 ∨ v9391 s i = 1) = true) ↔ (v834 s i) = (v3971 s i)
  simp [v0, v1, v4, v694, v830, v831, v832, v833, v834, v955, v956, v3971, v9384, v9385, v9386, v9387, v9388, v9389, v9390, v9391, v9392, v9393, reset, committed]

theorem register_task_12_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨20, by decide⟩ s i ↔
      (step s i).g1.r33_ndut_5Fdpath_5FregFile_5Fregs_5F12 = (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9403 s i ≠ 1 ∨ v9401 s i = 1) = true) ↔ (v840 s i) = (v4125 s i)
  simp [v0, v1, v4, v694, v836, v837, v838, v839, v840, v955, v956, v4125, v9394, v9395, v9396, v9397, v9398, v9399, v9400, v9401, v9402, v9403, reset, committed]

theorem register_task_13_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨21, by decide⟩ s i ↔
      (step s i).g1.r34_ndut_5Fdpath_5FregFile_5Fregs_5F13 = (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9413 s i ≠ 1 ∨ v9411 s i = 1) = true) ↔ (v846 s i) = (v4279 s i)
  simp [v0, v1, v4, v694, v842, v843, v844, v845, v846, v955, v956, v4279, v9404, v9405, v9406, v9407, v9408, v9409, v9410, v9411, v9412, v9413, reset, committed]

theorem register_task_14_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨22, by decide⟩ s i ↔
      (step s i).g1.r35_ndut_5Fdpath_5FregFile_5Fregs_5F14 = (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9423 s i ≠ 1 ∨ v9421 s i = 1) = true) ↔ (v852 s i) = (v4433 s i)
  simp [v0, v1, v4, v694, v848, v849, v850, v851, v852, v955, v956, v4433, v9414, v9415, v9416, v9417, v9418, v9419, v9420, v9421, v9422, v9423, reset, committed]

theorem register_task_15_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨23, by decide⟩ s i ↔
      (step s i).g1.r36_ndut_5Fdpath_5FregFile_5Fregs_5F15 = (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9433 s i ≠ 1 ∨ v9431 s i = 1) = true) ↔ (v858 s i) = (v4587 s i)
  simp [v0, v1, v4, v694, v854, v855, v856, v857, v858, v955, v956, v4587, v9424, v9425, v9426, v9427, v9428, v9429, v9430, v9431, v9432, v9433, reset, committed]

theorem register_task_16_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨24, by decide⟩ s i ↔
      (step s i).g1.r37_ndut_5Fdpath_5FregFile_5Fregs_5F16 = (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9442 s i ≠ 1 ∨ v9440 s i = 1) = true) ↔ (v864 s i) = (v4705 s i)
  simp [v0, v1, v4, v694, v860, v861, v862, v863, v864, v955, v956, v4705, v9434, v9435, v9436, v9437, v9438, v9439, v9440, v9441, v9442, reset, committed]

theorem register_task_17_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨25, by decide⟩ s i ↔
      (step s i).g1.r38_ndut_5Fdpath_5FregFile_5Fregs_5F17 = (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9451 s i ≠ 1 ∨ v9449 s i = 1) = true) ↔ (v870 s i) = (v4823 s i)
  simp [v0, v1, v4, v694, v866, v867, v868, v869, v870, v955, v956, v4823, v9443, v9444, v9445, v9446, v9447, v9448, v9449, v9450, v9451, reset, committed]

theorem register_task_18_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨26, by decide⟩ s i ↔
      (step s i).g1.r39_ndut_5Fdpath_5FregFile_5Fregs_5F18 = (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9460 s i ≠ 1 ∨ v9458 s i = 1) = true) ↔ (v876 s i) = (v4941 s i)
  simp [v0, v1, v4, v694, v872, v873, v874, v875, v876, v955, v956, v4941, v9452, v9453, v9454, v9455, v9456, v9457, v9458, v9459, v9460, reset, committed]

theorem register_task_19_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨27, by decide⟩ s i ↔
      (step s i).g1.r40_ndut_5Fdpath_5FregFile_5Fregs_5F19 = (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9469 s i ≠ 1 ∨ v9467 s i = 1) = true) ↔ (v882 s i) = (v5059 s i)
  simp [v0, v1, v4, v694, v878, v879, v880, v881, v882, v955, v956, v5059, v9461, v9462, v9463, v9464, v9465, v9466, v9467, v9468, v9469, reset, committed]

theorem register_task_20_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨28, by decide⟩ s i ↔
      (step s i).g1.r41_ndut_5Fdpath_5FregFile_5Fregs_5F20 = (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9478 s i ≠ 1 ∨ v9476 s i = 1) = true) ↔ (v888 s i) = (v5177 s i)
  simp [v0, v1, v4, v694, v884, v885, v886, v887, v888, v955, v956, v5177, v9470, v9471, v9472, v9473, v9474, v9475, v9476, v9477, v9478, reset, committed]

theorem register_task_21_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨29, by decide⟩ s i ↔
      (step s i).g1.r42_ndut_5Fdpath_5FregFile_5Fregs_5F21 = (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9487 s i ≠ 1 ∨ v9485 s i = 1) = true) ↔ (v894 s i) = (v5295 s i)
  simp [v0, v1, v4, v694, v890, v891, v892, v893, v894, v955, v956, v5295, v9479, v9480, v9481, v9482, v9483, v9484, v9485, v9486, v9487, reset, committed]

theorem register_task_22_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨30, by decide⟩ s i ↔
      (step s i).g1.r43_ndut_5Fdpath_5FregFile_5Fregs_5F22 = (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9496 s i ≠ 1 ∨ v9494 s i = 1) = true) ↔ (v900 s i) = (v5413 s i)
  simp [v0, v1, v4, v694, v896, v897, v898, v899, v900, v955, v956, v5413, v9488, v9489, v9490, v9491, v9492, v9493, v9494, v9495, v9496, reset, committed]

theorem register_task_23_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨31, by decide⟩ s i ↔
      (step s i).g1.r44_ndut_5Fdpath_5FregFile_5Fregs_5F23 = (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9505 s i ≠ 1 ∨ v9503 s i = 1) = true) ↔ (v906 s i) = (v5531 s i)
  simp [v0, v1, v4, v694, v902, v903, v904, v905, v906, v955, v956, v5531, v9497, v9498, v9499, v9500, v9501, v9502, v9503, v9504, v9505, reset, committed]

theorem register_task_24_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨32, by decide⟩ s i ↔
      (step s i).g1.r45_ndut_5Fdpath_5FregFile_5Fregs_5F24 = (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9514 s i ≠ 1 ∨ v9512 s i = 1) = true) ↔ (v912 s i) = (v5649 s i)
  simp [v0, v1, v4, v694, v908, v909, v910, v911, v912, v955, v956, v5649, v9506, v9507, v9508, v9509, v9510, v9511, v9512, v9513, v9514, reset, committed]

theorem register_task_25_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨33, by decide⟩ s i ↔
      (step s i).g1.r46_ndut_5Fdpath_5FregFile_5Fregs_5F25 = (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9523 s i ≠ 1 ∨ v9521 s i = 1) = true) ↔ (v918 s i) = (v5767 s i)
  simp [v0, v1, v4, v694, v914, v915, v916, v917, v918, v955, v956, v5767, v9515, v9516, v9517, v9518, v9519, v9520, v9521, v9522, v9523, reset, committed]

theorem register_task_26_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨34, by decide⟩ s i ↔
      (step s i).g1.r47_ndut_5Fdpath_5FregFile_5Fregs_5F26 = (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9532 s i ≠ 1 ∨ v9530 s i = 1) = true) ↔ (v924 s i) = (v5885 s i)
  simp [v0, v1, v4, v694, v920, v921, v922, v923, v924, v955, v956, v5885, v9524, v9525, v9526, v9527, v9528, v9529, v9530, v9531, v9532, reset, committed]

theorem register_task_27_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨35, by decide⟩ s i ↔
      (step s i).g1.r48_ndut_5Fdpath_5FregFile_5Fregs_5F27 = (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9541 s i ≠ 1 ∨ v9539 s i = 1) = true) ↔ (v930 s i) = (v6003 s i)
  simp [v0, v1, v4, v694, v926, v927, v928, v929, v930, v955, v956, v6003, v9533, v9534, v9535, v9536, v9537, v9538, v9539, v9540, v9541, reset, committed]

theorem register_task_28_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨36, by decide⟩ s i ↔
      (step s i).g1.r49_ndut_5Fdpath_5FregFile_5Fregs_5F28 = (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9550 s i ≠ 1 ∨ v9548 s i = 1) = true) ↔ (v936 s i) = (v6121 s i)
  simp [v0, v1, v4, v694, v932, v933, v934, v935, v936, v955, v956, v6121, v9542, v9543, v9544, v9545, v9546, v9547, v9548, v9549, v9550, reset, committed]

theorem register_task_29_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨37, by decide⟩ s i ↔
      (step s i).g1.r50_ndut_5Fdpath_5FregFile_5Fregs_5F29 = (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9559 s i ≠ 1 ∨ v9557 s i = 1) = true) ↔ (v942 s i) = (v6239 s i)
  simp [v0, v1, v4, v694, v938, v939, v940, v941, v942, v955, v956, v6239, v9551, v9552, v9553, v9554, v9555, v9556, v9557, v9558, v9559, reset, committed]

theorem register_task_30_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨38, by decide⟩ s i ↔
      (step s i).g1.r51_ndut_5Fdpath_5FregFile_5Fregs_5F30 = (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9568 s i ≠ 1 ∨ v9566 s i = 1) = true) ↔ (v948 s i) = (v6357 s i)
  simp [v0, v1, v4, v694, v944, v945, v946, v947, v948, v955, v956, v6357, v9560, v9561, v9562, v9563, v9564, v9565, v9566, v9567, v9568, reset, committed]

theorem register_task_31_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨39, by decide⟩ s i ↔
      (step s i).g1.r52_ndut_5Fdpath_5FregFile_5Fregs_5F31 = (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 := by
  have committed : v962 s i = 1 := commit
  change (decide (v9577 s i ≠ 1 ∨ v9575 s i = 1) = true) ↔ (v954 s i) = (v6475 s i)
  simp [v0, v1, v4, v694, v950, v951, v952, v953, v954, v955, v956, v6475, v9569, v9570, v9571, v9572, v9573, v9574, v9575, v9576, v9577, reset, committed]

def RegisterTasks (s : State) (i : Inputs) : Prop :=
  TaskHolds ⟨9, by decide⟩ s i ∧
  TaskHolds ⟨10, by decide⟩ s i ∧
  TaskHolds ⟨11, by decide⟩ s i ∧
  TaskHolds ⟨12, by decide⟩ s i ∧
  TaskHolds ⟨13, by decide⟩ s i ∧
  TaskHolds ⟨14, by decide⟩ s i ∧
  TaskHolds ⟨15, by decide⟩ s i ∧
  TaskHolds ⟨16, by decide⟩ s i ∧
  TaskHolds ⟨17, by decide⟩ s i ∧
  TaskHolds ⟨18, by decide⟩ s i ∧
  TaskHolds ⟨19, by decide⟩ s i ∧
  TaskHolds ⟨20, by decide⟩ s i ∧
  TaskHolds ⟨21, by decide⟩ s i ∧
  TaskHolds ⟨22, by decide⟩ s i ∧
  TaskHolds ⟨23, by decide⟩ s i ∧
  TaskHolds ⟨24, by decide⟩ s i ∧
  TaskHolds ⟨25, by decide⟩ s i ∧
  TaskHolds ⟨26, by decide⟩ s i ∧
  TaskHolds ⟨27, by decide⟩ s i ∧
  TaskHolds ⟨28, by decide⟩ s i ∧
  TaskHolds ⟨29, by decide⟩ s i ∧
  TaskHolds ⟨30, by decide⟩ s i ∧
  TaskHolds ⟨31, by decide⟩ s i ∧
  TaskHolds ⟨32, by decide⟩ s i ∧
  TaskHolds ⟨33, by decide⟩ s i ∧
  TaskHolds ⟨34, by decide⟩ s i ∧
  TaskHolds ⟨35, by decide⟩ s i ∧
  TaskHolds ⟨36, by decide⟩ s i ∧
  TaskHolds ⟨37, by decide⟩ s i ∧
  TaskHolds ⟨38, by decide⟩ s i ∧
  TaskHolds ⟨39, by decide⟩ s i

theorem register_tasks_iff_next (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    RegisterTasks s i ↔ RegisterAgreement (step s i) := by
  constructor
  · intro tasks
    rcases tasks with ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, h19, h20, h21, h22, h23, h24, h25, h26, h27, h28, h29, h30, h31⟩
    constructor
    · exact (register_task_1_iff_next s i reset commit).mp h1
    · exact (register_task_2_iff_next s i reset commit).mp h2
    · exact (register_task_3_iff_next s i reset commit).mp h3
    · exact (register_task_4_iff_next s i reset commit).mp h4
    · exact (register_task_5_iff_next s i reset commit).mp h5
    · exact (register_task_6_iff_next s i reset commit).mp h6
    · exact (register_task_7_iff_next s i reset commit).mp h7
    · exact (register_task_8_iff_next s i reset commit).mp h8
    · exact (register_task_9_iff_next s i reset commit).mp h9
    · exact (register_task_10_iff_next s i reset commit).mp h10
    · exact (register_task_11_iff_next s i reset commit).mp h11
    · exact (register_task_12_iff_next s i reset commit).mp h12
    · exact (register_task_13_iff_next s i reset commit).mp h13
    · exact (register_task_14_iff_next s i reset commit).mp h14
    · exact (register_task_15_iff_next s i reset commit).mp h15
    · exact (register_task_16_iff_next s i reset commit).mp h16
    · exact (register_task_17_iff_next s i reset commit).mp h17
    · exact (register_task_18_iff_next s i reset commit).mp h18
    · exact (register_task_19_iff_next s i reset commit).mp h19
    · exact (register_task_20_iff_next s i reset commit).mp h20
    · exact (register_task_21_iff_next s i reset commit).mp h21
    · exact (register_task_22_iff_next s i reset commit).mp h22
    · exact (register_task_23_iff_next s i reset commit).mp h23
    · exact (register_task_24_iff_next s i reset commit).mp h24
    · exact (register_task_25_iff_next s i reset commit).mp h25
    · exact (register_task_26_iff_next s i reset commit).mp h26
    · exact (register_task_27_iff_next s i reset commit).mp h27
    · exact (register_task_28_iff_next s i reset commit).mp h28
    · exact (register_task_29_iff_next s i reset commit).mp h29
    · exact (register_task_30_iff_next s i reset commit).mp h30
    · exact (register_task_31_iff_next s i reset commit).mp h31
  · intro agree
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (register_task_1_iff_next s i reset commit).mpr agree.x1
    · exact (register_task_2_iff_next s i reset commit).mpr agree.x2
    · exact (register_task_3_iff_next s i reset commit).mpr agree.x3
    · exact (register_task_4_iff_next s i reset commit).mpr agree.x4
    · exact (register_task_5_iff_next s i reset commit).mpr agree.x5
    · exact (register_task_6_iff_next s i reset commit).mpr agree.x6
    · exact (register_task_7_iff_next s i reset commit).mpr agree.x7
    · exact (register_task_8_iff_next s i reset commit).mpr agree.x8
    · exact (register_task_9_iff_next s i reset commit).mpr agree.x9
    · exact (register_task_10_iff_next s i reset commit).mpr agree.x10
    · exact (register_task_11_iff_next s i reset commit).mpr agree.x11
    · exact (register_task_12_iff_next s i reset commit).mpr agree.x12
    · exact (register_task_13_iff_next s i reset commit).mpr agree.x13
    · exact (register_task_14_iff_next s i reset commit).mpr agree.x14
    · exact (register_task_15_iff_next s i reset commit).mpr agree.x15
    · exact (register_task_16_iff_next s i reset commit).mpr agree.x16
    · exact (register_task_17_iff_next s i reset commit).mpr agree.x17
    · exact (register_task_18_iff_next s i reset commit).mpr agree.x18
    · exact (register_task_19_iff_next s i reset commit).mpr agree.x19
    · exact (register_task_20_iff_next s i reset commit).mpr agree.x20
    · exact (register_task_21_iff_next s i reset commit).mpr agree.x21
    · exact (register_task_22_iff_next s i reset commit).mpr agree.x22
    · exact (register_task_23_iff_next s i reset commit).mpr agree.x23
    · exact (register_task_24_iff_next s i reset commit).mpr agree.x24
    · exact (register_task_25_iff_next s i reset commit).mpr agree.x25
    · exact (register_task_26_iff_next s i reset commit).mpr agree.x26
    · exact (register_task_27_iff_next s i reset commit).mpr agree.x27
    · exact (register_task_28_iff_next s i reset commit).mpr agree.x28
    · exact (register_task_29_iff_next s i reset commit).mpr agree.x29
    · exact (register_task_30_iff_next s i reset commit).mpr agree.x30
    · exact (register_task_31_iff_next s i reset commit).mpr agree.x31
#print axioms register_tasks_iff_next
end RiscvMiniProofs
