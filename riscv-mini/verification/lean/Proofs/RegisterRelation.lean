import Proofs.Contract

namespace RiscvMiniProofs
open nCoreSoc

-- x0 is handled independently by ZeroRegister; these are x1 through x31.
structure RegisterAgreement (s : State) : Prop where
  x1 : s.g0.r22_ndut_5Fdpath_5FregFile_5Fregs_5F1 = s.g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1
  x2 : s.g0.r23_ndut_5Fdpath_5FregFile_5Fregs_5F2 = s.g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2
  x3 : s.g0.r24_ndut_5Fdpath_5FregFile_5Fregs_5F3 = s.g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3
  x4 : s.g0.r25_ndut_5Fdpath_5FregFile_5Fregs_5F4 = s.g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4
  x5 : s.g0.r26_ndut_5Fdpath_5FregFile_5Fregs_5F5 = s.g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5
  x6 : s.g0.r27_ndut_5Fdpath_5FregFile_5Fregs_5F6 = s.g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6
  x7 : s.g0.r28_ndut_5Fdpath_5FregFile_5Fregs_5F7 = s.g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7
  x8 : s.g0.r29_ndut_5Fdpath_5FregFile_5Fregs_5F8 = s.g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8
  x9 : s.g0.r30_ndut_5Fdpath_5FregFile_5Fregs_5F9 = s.g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9
  x10 : s.g0.r31_ndut_5Fdpath_5FregFile_5Fregs_5F10 = s.g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10
  x11 : s.g1.r32_ndut_5Fdpath_5FregFile_5Fregs_5F11 = s.g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11
  x12 : s.g1.r33_ndut_5Fdpath_5FregFile_5Fregs_5F12 = s.g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12
  x13 : s.g1.r34_ndut_5Fdpath_5FregFile_5Fregs_5F13 = s.g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13
  x14 : s.g1.r35_ndut_5Fdpath_5FregFile_5Fregs_5F14 = s.g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14
  x15 : s.g1.r36_ndut_5Fdpath_5FregFile_5Fregs_5F15 = s.g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15
  x16 : s.g1.r37_ndut_5Fdpath_5FregFile_5Fregs_5F16 = s.g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16
  x17 : s.g1.r38_ndut_5Fdpath_5FregFile_5Fregs_5F17 = s.g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17
  x18 : s.g1.r39_ndut_5Fdpath_5FregFile_5Fregs_5F18 = s.g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18
  x19 : s.g1.r40_ndut_5Fdpath_5FregFile_5Fregs_5F19 = s.g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19
  x20 : s.g1.r41_ndut_5Fdpath_5FregFile_5Fregs_5F20 = s.g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20
  x21 : s.g1.r42_ndut_5Fdpath_5FregFile_5Fregs_5F21 = s.g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21
  x22 : s.g1.r43_ndut_5Fdpath_5FregFile_5Fregs_5F22 = s.g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22
  x23 : s.g1.r44_ndut_5Fdpath_5FregFile_5Fregs_5F23 = s.g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23
  x24 : s.g1.r45_ndut_5Fdpath_5FregFile_5Fregs_5F24 = s.g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24
  x25 : s.g1.r46_ndut_5Fdpath_5FregFile_5Fregs_5F25 = s.g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25
  x26 : s.g1.r47_ndut_5Fdpath_5FregFile_5Fregs_5F26 = s.g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26
  x27 : s.g1.r48_ndut_5Fdpath_5FregFile_5Fregs_5F27 = s.g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27
  x28 : s.g1.r49_ndut_5Fdpath_5FregFile_5Fregs_5F28 = s.g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28
  x29 : s.g1.r50_ndut_5Fdpath_5FregFile_5Fregs_5F29 = s.g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29
  x30 : s.g1.r51_ndut_5Fdpath_5FregFile_5Fregs_5F30 = s.g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30
  x31 : s.g1.r52_ndut_5Fdpath_5FregFile_5Fregs_5F31 = s.g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31

theorem registers_agree_after_reset (s : State) (i : Inputs)
    (reset : i.nreset = 1) : RegisterAgreement (step s i) := by
  constructor
  · change (v774 s i) = (v2431 s i)
    simp [v0, v1, v694, v769, v774, v955, v956, v970, v971, v2431, reset, ↓reduceIte]
  · change (v780 s i) = (v2585 s i)
    simp [v0, v1, v694, v775, v780, v955, v956, v2432, v2433, v2585, reset, ↓reduceIte]
  · change (v786 s i) = (v2739 s i)
    simp [v0, v1, v694, v781, v786, v955, v956, v2586, v2587, v2739, reset, ↓reduceIte]
  · change (v792 s i) = (v2893 s i)
    simp [v0, v1, v694, v787, v792, v955, v956, v2740, v2741, v2893, reset, ↓reduceIte]
  · change (v798 s i) = (v3047 s i)
    simp [v0, v1, v694, v793, v798, v955, v956, v2894, v2895, v3047, reset, ↓reduceIte]
  · change (v804 s i) = (v3201 s i)
    simp [v0, v1, v694, v799, v804, v955, v956, v3048, v3049, v3201, reset, ↓reduceIte]
  · change (v810 s i) = (v3355 s i)
    simp [v0, v1, v694, v805, v810, v955, v956, v3202, v3203, v3355, reset, ↓reduceIte]
  · change (v816 s i) = (v3509 s i)
    simp [v0, v1, v694, v811, v816, v955, v956, v3356, v3357, v3509, reset, ↓reduceIte]
  · change (v822 s i) = (v3663 s i)
    simp [v0, v1, v694, v817, v822, v955, v956, v3510, v3511, v3663, reset, ↓reduceIte]
  · change (v828 s i) = (v3817 s i)
    simp [v0, v1, v694, v823, v828, v955, v956, v3664, v3665, v3817, reset, ↓reduceIte]
  · change (v834 s i) = (v3971 s i)
    simp [v0, v1, v694, v829, v834, v955, v956, v3818, v3819, v3971, reset, ↓reduceIte]
  · change (v840 s i) = (v4125 s i)
    simp [v0, v1, v694, v835, v840, v955, v956, v3972, v3973, v4125, reset, ↓reduceIte]
  · change (v846 s i) = (v4279 s i)
    simp [v0, v1, v694, v841, v846, v955, v956, v4126, v4127, v4279, reset, ↓reduceIte]
  · change (v852 s i) = (v4433 s i)
    simp [v0, v1, v694, v847, v852, v955, v956, v4280, v4281, v4433, reset, ↓reduceIte]
  · change (v858 s i) = (v4587 s i)
    simp [v0, v1, v694, v853, v858, v955, v956, v4434, v4435, v4587, reset, ↓reduceIte]
  · change (v864 s i) = (v4705 s i)
    simp [v0, v1, v694, v859, v864, v955, v956, v4588, v4589, v4705, reset, ↓reduceIte]
  · change (v870 s i) = (v4823 s i)
    simp [v0, v1, v694, v865, v870, v955, v956, v4706, v4707, v4823, reset, ↓reduceIte]
  · change (v876 s i) = (v4941 s i)
    simp [v0, v1, v694, v871, v876, v955, v956, v4824, v4825, v4941, reset, ↓reduceIte]
  · change (v882 s i) = (v5059 s i)
    simp [v0, v1, v694, v877, v882, v955, v956, v4942, v4943, v5059, reset, ↓reduceIte]
  · change (v888 s i) = (v5177 s i)
    simp [v0, v1, v694, v883, v888, v955, v956, v5060, v5061, v5177, reset, ↓reduceIte]
  · change (v894 s i) = (v5295 s i)
    simp [v0, v1, v694, v889, v894, v955, v956, v5178, v5179, v5295, reset, ↓reduceIte]
  · change (v900 s i) = (v5413 s i)
    simp [v0, v1, v694, v895, v900, v955, v956, v5296, v5297, v5413, reset, ↓reduceIte]
  · change (v906 s i) = (v5531 s i)
    simp [v0, v1, v694, v901, v906, v955, v956, v5414, v5415, v5531, reset, ↓reduceIte]
  · change (v912 s i) = (v5649 s i)
    simp [v0, v1, v694, v907, v912, v955, v956, v5532, v5533, v5649, reset, ↓reduceIte]
  · change (v918 s i) = (v5767 s i)
    simp [v0, v1, v694, v913, v918, v955, v956, v5650, v5651, v5767, reset, ↓reduceIte]
  · change (v924 s i) = (v5885 s i)
    simp [v0, v1, v694, v919, v924, v955, v956, v5768, v5769, v5885, reset, ↓reduceIte]
  · change (v930 s i) = (v6003 s i)
    simp [v0, v1, v694, v925, v930, v955, v956, v5886, v5887, v6003, reset, ↓reduceIte]
  · change (v936 s i) = (v6121 s i)
    simp [v0, v1, v694, v931, v936, v955, v956, v6004, v6005, v6121, reset, ↓reduceIte]
  · change (v942 s i) = (v6239 s i)
    simp [v0, v1, v694, v937, v942, v955, v956, v6122, v6123, v6239, reset, ↓reduceIte]
  · change (v948 s i) = (v6357 s i)
    simp [v0, v1, v694, v943, v948, v955, v956, v6240, v6241, v6357, reset, ↓reduceIte]
  · change (v954 s i) = (v6475 s i)
    simp [v0, v1, v694, v949, v954, v955, v956, v6358, v6359, v6475, reset, ↓reduceIte]

-- No assertion is assumed here. The no-write premise must be established
-- separately from the reachable pipeline state for a non-commit cycle.
theorem registers_agree_idle (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (reset : i.nreset = 0)
    (commit : v964 s i = 0) (write : v704 s i = 0) :
    RegisterAgreement (step s i) := by
  constructor
  · change (v774 s i) = (v2431 s i)
    simp [v0, v1, v694, v773, v774, v955, v956, v1504, v2429, v2430, v2431, reset, ↓reduceIte, commit, write, agree.x1]
  · change (v780 s i) = (v2585 s i)
    simp [v0, v1, v694, v779, v780, v955, v956, v1501, v2583, v2584, v2585, reset, ↓reduceIte, commit, write, agree.x2]
  · change (v786 s i) = (v2739 s i)
    simp [v0, v1, v694, v785, v786, v955, v956, v1498, v2737, v2738, v2739, reset, ↓reduceIte, commit, write, agree.x3]
  · change (v792 s i) = (v2893 s i)
    simp [v0, v1, v694, v791, v792, v955, v956, v1495, v2891, v2892, v2893, reset, ↓reduceIte, commit, write, agree.x4]
  · change (v798 s i) = (v3047 s i)
    simp [v0, v1, v694, v797, v798, v955, v956, v1492, v3045, v3046, v3047, reset, ↓reduceIte, commit, write, agree.x5]
  · change (v804 s i) = (v3201 s i)
    simp [v0, v1, v694, v803, v804, v955, v956, v1489, v3199, v3200, v3201, reset, ↓reduceIte, commit, write, agree.x6]
  · change (v810 s i) = (v3355 s i)
    simp [v0, v1, v694, v809, v810, v955, v956, v1486, v3353, v3354, v3355, reset, ↓reduceIte, commit, write, agree.x7]
  · change (v816 s i) = (v3509 s i)
    simp [v0, v1, v694, v815, v816, v955, v956, v1483, v3507, v3508, v3509, reset, ↓reduceIte, commit, write, agree.x8]
  · change (v822 s i) = (v3663 s i)
    simp [v0, v1, v694, v821, v822, v955, v956, v1480, v3661, v3662, v3663, reset, ↓reduceIte, commit, write, agree.x9]
  · change (v828 s i) = (v3817 s i)
    simp [v0, v1, v694, v827, v828, v955, v956, v1477, v3815, v3816, v3817, reset, ↓reduceIte, commit, write, agree.x10]
  · change (v834 s i) = (v3971 s i)
    simp [v0, v1, v694, v833, v834, v955, v956, v1474, v3969, v3970, v3971, reset, ↓reduceIte, commit, write, agree.x11]
  · change (v840 s i) = (v4125 s i)
    simp [v0, v1, v694, v839, v840, v955, v956, v1471, v4123, v4124, v4125, reset, ↓reduceIte, commit, write, agree.x12]
  · change (v846 s i) = (v4279 s i)
    simp [v0, v1, v694, v845, v846, v955, v956, v1468, v4277, v4278, v4279, reset, ↓reduceIte, commit, write, agree.x13]
  · change (v852 s i) = (v4433 s i)
    simp [v0, v1, v694, v851, v852, v955, v956, v1465, v4431, v4432, v4433, reset, ↓reduceIte, commit, write, agree.x14]
  · change (v858 s i) = (v4587 s i)
    simp [v0, v1, v694, v857, v858, v955, v956, v1462, v4585, v4586, v4587, reset, ↓reduceIte, commit, write, agree.x15]
  · change (v864 s i) = (v4705 s i)
    simp [v0, v1, v694, v863, v864, v955, v956, v1459, v4703, v4704, v4705, reset, ↓reduceIte, commit, write, agree.x16]
  · change (v870 s i) = (v4823 s i)
    simp [v0, v1, v694, v869, v870, v955, v956, v1457, v4821, v4822, v4823, reset, ↓reduceIte, commit, write, agree.x17]
  · change (v876 s i) = (v4941 s i)
    simp [v0, v1, v694, v875, v876, v955, v956, v1455, v4939, v4940, v4941, reset, ↓reduceIte, commit, write, agree.x18]
  · change (v882 s i) = (v5059 s i)
    simp [v0, v1, v694, v881, v882, v955, v956, v1453, v5057, v5058, v5059, reset, ↓reduceIte, commit, write, agree.x19]
  · change (v888 s i) = (v5177 s i)
    simp [v0, v1, v694, v887, v888, v955, v956, v1451, v5175, v5176, v5177, reset, ↓reduceIte, commit, write, agree.x20]
  · change (v894 s i) = (v5295 s i)
    simp [v0, v1, v694, v893, v894, v955, v956, v1449, v5293, v5294, v5295, reset, ↓reduceIte, commit, write, agree.x21]
  · change (v900 s i) = (v5413 s i)
    simp [v0, v1, v694, v899, v900, v955, v956, v1447, v5411, v5412, v5413, reset, ↓reduceIte, commit, write, agree.x22]
  · change (v906 s i) = (v5531 s i)
    simp [v0, v1, v694, v905, v906, v955, v956, v1445, v5529, v5530, v5531, reset, ↓reduceIte, commit, write, agree.x23]
  · change (v912 s i) = (v5649 s i)
    simp [v0, v1, v694, v911, v912, v955, v956, v1443, v5647, v5648, v5649, reset, ↓reduceIte, commit, write, agree.x24]
  · change (v918 s i) = (v5767 s i)
    simp [v0, v1, v694, v917, v918, v955, v956, v1441, v5765, v5766, v5767, reset, ↓reduceIte, commit, write, agree.x25]
  · change (v924 s i) = (v5885 s i)
    simp [v0, v1, v694, v923, v924, v955, v956, v1439, v5883, v5884, v5885, reset, ↓reduceIte, commit, write, agree.x26]
  · change (v930 s i) = (v6003 s i)
    simp [v0, v1, v694, v929, v930, v955, v956, v1437, v6001, v6002, v6003, reset, ↓reduceIte, commit, write, agree.x27]
  · change (v936 s i) = (v6121 s i)
    simp [v0, v1, v694, v935, v936, v955, v956, v1435, v6119, v6120, v6121, reset, ↓reduceIte, commit, write, agree.x28]
  · change (v942 s i) = (v6239 s i)
    simp [v0, v1, v694, v941, v942, v955, v956, v1433, v6237, v6238, v6239, reset, ↓reduceIte, commit, write, agree.x29]
  · change (v948 s i) = (v6357 s i)
    simp [v0, v1, v694, v947, v948, v955, v956, v1431, v6355, v6356, v6357, reset, ↓reduceIte, commit, write, agree.x30]
  · change (v954 s i) = (v6475 s i)
    simp [v0, v1, v694, v953, v954, v955, v956, v1429, v6473, v6474, v6475, reset, ↓reduceIte, commit, write, agree.x31]

-- The reset prefix establishes the relation at its final boundary,
-- for arbitrary initial state and arbitrary shared reset input values.
theorem registers_agree_at_reset_boundary (initial : State)
    (inputs : Nat → Inputs) (cycles : Nat) (reset : ResetPrefix inputs cycles) :
    RegisterAgreement (run initial inputs cycles) := by
  cases cycles with
  | zero => have := reset.1; omega
  | succ n =>
    simp only [run]
    exact registers_agree_after_reset _ _ (reset.2.1 n (Nat.lt_succ_self n))

#print axioms registers_agree_at_reset_boundary
#print axioms registers_agree_idle
end RiscvMiniProofs
