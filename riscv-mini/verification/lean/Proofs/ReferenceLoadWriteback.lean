import Proofs.ReferenceReads
import Proofs.ReferenceLoadDecode
import Proofs.MaskFacts
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
private theorem reference_commit_instruction (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v977 s i = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by simp [v977, v975, v974, v973, commit]
private theorem ref_lb_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 3 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lb_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 3 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lb_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 3 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lb_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 3 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lb_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 3 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lb_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 3 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lb_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 3 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lb_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 3 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lb_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 3 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lb_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) : v1098 s i = 1 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 3 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_lb_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 3 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lb_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 3 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lb_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 3 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reference_lb_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2193 s i := by
  change (v2431 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v2177, v2178, v2400, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2193 s i := by
  change (v2585 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v2458, v2459, v2554, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2193 s i := by
  change (v2739 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v2612, v2613, v2708, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2193 s i := by
  change (v2893 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v2766, v2767, v2862, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2193 s i := by
  change (v3047 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v2920, v2921, v3016, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2193 s i := by
  change (v3201 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v3074, v3075, v3170, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2193 s i := by
  change (v3355 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v3228, v3229, v3324, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2193 s i := by
  change (v3509 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v3382, v3383, v3478, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2193 s i := by
  change (v3663 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v3536, v3537, v3632, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2193 s i := by
  change (v3817 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v3690, v3691, v3786, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2193 s i := by
  change (v3971 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v3844, v3845, v3940, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2193 s i := by
  change (v4125 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v3998, v3999, v4094, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2193 s i := by
  change (v4279 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v4152, v4153, v4248, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2193 s i := by
  change (v4433 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v4306, v4307, v4402, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2193 s i := by
  change (v4587 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v4460, v4461, v4556, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2193 s i := by
  change (v4705 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v4602, v4674, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2193 s i := by
  change (v4823 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v4720, v4792, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2193 s i := by
  change (v4941 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v4838, v4910, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2193 s i := by
  change (v5059 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v4956, v5028, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2193 s i := by
  change (v5177 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v5074, v5146, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2193 s i := by
  change (v5295 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v5192, v5264, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2193 s i := by
  change (v5413 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v5310, v5382, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2193 s i := by
  change (v5531 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v5428, v5500, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2193 s i := by
  change (v5649 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v5546, v5618, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2193 s i := by
  change (v5767 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v5664, v5736, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2193 s i := by
  change (v5885 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v5782, v5854, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2193 s i := by
  change (v6003 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v5900, v5972, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2193 s i := by
  change (v6121 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v6018, v6090, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2193 s i := by
  change (v6239 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v6136, v6208, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2193 s i := by
  change (v6357 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v6254, v6326, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
private theorem reference_lb_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2193 s i := by
  change (v6475 s i) = v2193 s i
  simp [v0, v1, ref_lb_v1005 s i commit known, ref_lb_v1013 s i commit known, ref_lb_v1021 s i commit known, ref_lb_v1029 s i commit known, ref_lb_v1037 s i commit known, ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v6372, v6444, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_lb_v980 s i commit known, ref_lb_v989 s i commit known, ref_lb_v997 s i commit known, reset, target]
theorem reference_lb_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2193 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x1 s i reset commit known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x2 s i reset commit known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x3 s i reset commit known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x4 s i reset commit known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x5 s i reset commit known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x6 s i reset commit known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x7 s i reset commit known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x8 s i reset commit known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x9 s i reset commit known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x10 s i reset commit known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x11 s i reset commit known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x12 s i reset commit known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x13 s i reset commit known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x14 s i reset commit known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x15 s i reset commit known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x16 s i reset commit known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x17 s i reset commit known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x18 s i reset commit known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x19 s i reset commit known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x20 s i reset commit known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x21 s i reset commit known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x22 s i reset commit known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x23 s i reset commit known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x24 s i reset commit known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x25 s i reset commit known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x26 s i reset commit known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x27 s i reset commit known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x28 s i reset commit known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x29 s i reset commit known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x30 s i reset commit known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_lb_rd s i commit known).trans target
    rw [target]
    exact reference_lb_next_x31 s i reset commit known refTarget
#print axioms reference_lb_written_value
private theorem ref_lh_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4099 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lh_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4099 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lh_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4099 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lh_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4099 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lh_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4099 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lh_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4099 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lh_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4099 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lh_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4099 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lh_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) : v1090 s i = 1 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4099 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_lh_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4099 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lh_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4099 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lh_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4099 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reference_lh_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2176 s i := by
  change (v2431 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v2160, v2161, v2402, v2403, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2176 s i := by
  change (v2585 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v2456, v2457, v2556, v2557, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2176 s i := by
  change (v2739 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v2610, v2611, v2710, v2711, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2176 s i := by
  change (v2893 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v2764, v2765, v2864, v2865, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2176 s i := by
  change (v3047 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v2918, v2919, v3018, v3019, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2176 s i := by
  change (v3201 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v3072, v3073, v3172, v3173, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2176 s i := by
  change (v3355 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v3226, v3227, v3326, v3327, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2176 s i := by
  change (v3509 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v3380, v3381, v3480, v3481, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2176 s i := by
  change (v3663 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v3534, v3535, v3634, v3635, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2176 s i := by
  change (v3817 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v3688, v3689, v3788, v3789, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2176 s i := by
  change (v3971 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v3842, v3843, v3942, v3943, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2176 s i := by
  change (v4125 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v3996, v3997, v4096, v4097, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2176 s i := by
  change (v4279 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v4150, v4151, v4250, v4251, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2176 s i := by
  change (v4433 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v4304, v4305, v4404, v4405, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2176 s i := by
  change (v4587 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v4458, v4459, v4558, v4559, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2176 s i := by
  change (v4705 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v4601, v4676, v4677, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2176 s i := by
  change (v4823 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v4719, v4794, v4795, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2176 s i := by
  change (v4941 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v4837, v4912, v4913, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2176 s i := by
  change (v5059 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v4955, v5030, v5031, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2176 s i := by
  change (v5177 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v5073, v5148, v5149, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2176 s i := by
  change (v5295 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v5191, v5266, v5267, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2176 s i := by
  change (v5413 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v5309, v5384, v5385, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2176 s i := by
  change (v5531 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v5427, v5502, v5503, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2176 s i := by
  change (v5649 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v5545, v5620, v5621, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2176 s i := by
  change (v5767 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v5663, v5738, v5739, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2176 s i := by
  change (v5885 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v5781, v5856, v5857, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2176 s i := by
  change (v6003 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v5899, v5974, v5975, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2176 s i := by
  change (v6121 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v6017, v6092, v6093, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2176 s i := by
  change (v6239 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v6135, v6210, v6211, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2176 s i := by
  change (v6357 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v6253, v6328, v6329, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
private theorem reference_lh_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2176 s i := by
  change (v6475 s i) = v2176 s i
  simp [v0, v1, ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v6371, v6446, v6447, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, reset, target]
theorem reference_lh_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2159 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2176 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x1 s i reset commit aligned known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x2 s i reset commit aligned known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x3 s i reset commit aligned known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x4 s i reset commit aligned known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x5 s i reset commit aligned known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x6 s i reset commit aligned known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x7 s i reset commit aligned known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x8 s i reset commit aligned known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x9 s i reset commit aligned known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x10 s i reset commit aligned known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x11 s i reset commit aligned known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x12 s i reset commit aligned known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x13 s i reset commit aligned known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x14 s i reset commit aligned known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x15 s i reset commit aligned known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x16 s i reset commit aligned known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x17 s i reset commit aligned known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x18 s i reset commit aligned known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x19 s i reset commit aligned known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x20 s i reset commit aligned known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x21 s i reset commit aligned known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x22 s i reset commit aligned known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x23 s i reset commit aligned known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x24 s i reset commit aligned known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x25 s i reset commit aligned known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x26 s i reset commit aligned known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x27 s i reset commit aligned known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x28 s i reset commit aligned known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x29 s i reset commit aligned known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x30 s i reset commit aligned known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_lh_rd s i commit known).trans target
    rw [target]
    exact reference_lh_next_x31 s i reset commit aligned known refTarget
#print axioms reference_lh_written_value
private theorem ref_lw_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8195 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lw_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8195 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lw_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8195 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lw_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8195 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lw_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8195 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lw_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8195 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lw_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8195 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lw_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) : v1082 s i = 1 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8195 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_lw_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8195 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lw_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8195 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lw_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8195 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reference_lw_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2153 s i := by
  change (v2431 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v2140, v2141, v2405, v2406, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2153 s i := by
  change (v2585 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v2454, v2455, v2559, v2560, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2153 s i := by
  change (v2739 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v2608, v2609, v2713, v2714, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2153 s i := by
  change (v2893 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v2762, v2763, v2867, v2868, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2153 s i := by
  change (v3047 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v2916, v2917, v3021, v3022, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2153 s i := by
  change (v3201 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v3070, v3071, v3175, v3176, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2153 s i := by
  change (v3355 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v3224, v3225, v3329, v3330, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2153 s i := by
  change (v3509 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v3378, v3379, v3483, v3484, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2153 s i := by
  change (v3663 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v3532, v3533, v3637, v3638, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2153 s i := by
  change (v3817 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v3686, v3687, v3791, v3792, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2153 s i := by
  change (v3971 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v3840, v3841, v3945, v3946, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2153 s i := by
  change (v4125 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v3994, v3995, v4099, v4100, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2153 s i := by
  change (v4279 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v4148, v4149, v4253, v4254, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2153 s i := by
  change (v4433 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v4302, v4303, v4407, v4408, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2153 s i := by
  change (v4587 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v4456, v4457, v4561, v4562, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2153 s i := by
  change (v4705 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v4600, v4679, v4680, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2153 s i := by
  change (v4823 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v4718, v4797, v4798, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2153 s i := by
  change (v4941 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v4836, v4915, v4916, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2153 s i := by
  change (v5059 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v4954, v5033, v5034, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2153 s i := by
  change (v5177 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v5072, v5151, v5152, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2153 s i := by
  change (v5295 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v5190, v5269, v5270, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2153 s i := by
  change (v5413 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v5308, v5387, v5388, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2153 s i := by
  change (v5531 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v5426, v5505, v5506, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2153 s i := by
  change (v5649 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v5544, v5623, v5624, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2153 s i := by
  change (v5767 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v5662, v5741, v5742, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2153 s i := by
  change (v5885 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v5780, v5859, v5860, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2153 s i := by
  change (v6003 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v5898, v5977, v5978, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2153 s i := by
  change (v6121 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v6016, v6095, v6096, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2153 s i := by
  change (v6239 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v6134, v6213, v6214, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2153 s i := by
  change (v6357 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v6252, v6331, v6332, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
private theorem reference_lw_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2153 s i := by
  change (v6475 s i) = v2153 s i
  simp [v0, v1, ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v6370, v6449, v6450, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, reset, target]
theorem reference_lw_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2139 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2153 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x1 s i reset commit aligned known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x2 s i reset commit aligned known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x3 s i reset commit aligned known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x4 s i reset commit aligned known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x5 s i reset commit aligned known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x6 s i reset commit aligned known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x7 s i reset commit aligned known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x8 s i reset commit aligned known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x9 s i reset commit aligned known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x10 s i reset commit aligned known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x11 s i reset commit aligned known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x12 s i reset commit aligned known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x13 s i reset commit aligned known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x14 s i reset commit aligned known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x15 s i reset commit aligned known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x16 s i reset commit aligned known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x17 s i reset commit aligned known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x18 s i reset commit aligned known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x19 s i reset commit aligned known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x20 s i reset commit aligned known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x21 s i reset commit aligned known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x22 s i reset commit aligned known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x23 s i reset commit aligned known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x24 s i reset commit aligned known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x25 s i reset commit aligned known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x26 s i reset commit aligned known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x27 s i reset commit aligned known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x28 s i reset commit aligned known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x29 s i reset commit aligned known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x30 s i reset commit aligned known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_lw_rd s i commit known).trans target
    rw [target]
    exact reference_lw_next_x31 s i reset commit aligned known refTarget
#print axioms reference_lw_written_value
private theorem ref_lbu_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16387 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lbu_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16387 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lbu_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16387 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lbu_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16387 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lbu_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16387 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lbu_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16387 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lbu_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) : v1074 s i = 1 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16387 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_lbu_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16387 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lbu_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16387 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lbu_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16387 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reference_lbu_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2132 s i := by
  change (v2431 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v2118, v2119, v2408, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2132 s i := by
  change (v2585 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v2452, v2453, v2562, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2132 s i := by
  change (v2739 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v2606, v2607, v2716, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2132 s i := by
  change (v2893 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v2760, v2761, v2870, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2132 s i := by
  change (v3047 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v2914, v2915, v3024, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2132 s i := by
  change (v3201 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v3068, v3069, v3178, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2132 s i := by
  change (v3355 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v3222, v3223, v3332, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2132 s i := by
  change (v3509 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v3376, v3377, v3486, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2132 s i := by
  change (v3663 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v3530, v3531, v3640, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2132 s i := by
  change (v3817 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v3684, v3685, v3794, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2132 s i := by
  change (v3971 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v3838, v3839, v3948, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2132 s i := by
  change (v4125 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v3992, v3993, v4102, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2132 s i := by
  change (v4279 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v4146, v4147, v4256, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2132 s i := by
  change (v4433 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v4300, v4301, v4410, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2132 s i := by
  change (v4587 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v4454, v4455, v4564, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2132 s i := by
  change (v4705 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v4599, v4682, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2132 s i := by
  change (v4823 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v4717, v4800, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2132 s i := by
  change (v4941 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v4835, v4918, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2132 s i := by
  change (v5059 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v4953, v5036, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2132 s i := by
  change (v5177 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v5071, v5154, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2132 s i := by
  change (v5295 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v5189, v5272, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2132 s i := by
  change (v5413 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v5307, v5390, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2132 s i := by
  change (v5531 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v5425, v5508, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2132 s i := by
  change (v5649 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v5543, v5626, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2132 s i := by
  change (v5767 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v5661, v5744, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2132 s i := by
  change (v5885 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v5779, v5862, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2132 s i := by
  change (v6003 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v5897, v5980, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2132 s i := by
  change (v6121 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v6015, v6098, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2132 s i := by
  change (v6239 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v6133, v6216, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2132 s i := by
  change (v6357 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v6251, v6334, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
private theorem reference_lbu_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2132 s i := by
  change (v6475 s i) = v2132 s i
  simp [v0, v1, ref_lbu_v1005 s i commit known, ref_lbu_v1013 s i commit known, ref_lbu_v1021 s i commit known, ref_lbu_v1029 s i commit known, ref_lbu_v1037 s i commit known, ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v6369, v6452, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_lbu_v980 s i commit known, ref_lbu_v989 s i commit known, ref_lbu_v997 s i commit known, reset, target]
theorem reference_lbu_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2132 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x1 s i reset commit known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x2 s i reset commit known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x3 s i reset commit known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x4 s i reset commit known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x5 s i reset commit known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x6 s i reset commit known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x7 s i reset commit known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x8 s i reset commit known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x9 s i reset commit known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x10 s i reset commit known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x11 s i reset commit known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x12 s i reset commit known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x13 s i reset commit known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x14 s i reset commit known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x15 s i reset commit known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x16 s i reset commit known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x17 s i reset commit known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x18 s i reset commit known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x19 s i reset commit known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x20 s i reset commit known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x21 s i reset commit known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x22 s i reset commit known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x23 s i reset commit known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x24 s i reset commit known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x25 s i reset commit known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x26 s i reset commit known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x27 s i reset commit known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x28 s i reset commit known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x29 s i reset commit known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x30 s i reset commit known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_lbu_rd s i commit known).trans target
    rw [target]
    exact reference_lbu_next_x31 s i reset commit known refTarget
#print axioms reference_lbu_written_value
private theorem ref_lhu_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20483 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lhu_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20483 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lhu_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20483 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lhu_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20483 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lhu_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20483 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lhu_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) : v1066 s i = 1 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20483 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_lhu_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20483 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lhu_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20483 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lhu_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20483 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem reference_lhu_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2117 s i := by
  change (v2431 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v2098, v2099, v2410, v2411, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2117 s i := by
  change (v2585 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v2450, v2451, v2564, v2565, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2117 s i := by
  change (v2739 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v2604, v2605, v2718, v2719, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2117 s i := by
  change (v2893 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v2758, v2759, v2872, v2873, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2117 s i := by
  change (v3047 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v2912, v2913, v3026, v3027, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2117 s i := by
  change (v3201 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v3066, v3067, v3180, v3181, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2117 s i := by
  change (v3355 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v3220, v3221, v3334, v3335, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2117 s i := by
  change (v3509 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v3374, v3375, v3488, v3489, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2117 s i := by
  change (v3663 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v3528, v3529, v3642, v3643, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2117 s i := by
  change (v3817 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v3682, v3683, v3796, v3797, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2117 s i := by
  change (v3971 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v3836, v3837, v3950, v3951, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2117 s i := by
  change (v4125 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v3990, v3991, v4104, v4105, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2117 s i := by
  change (v4279 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v4144, v4145, v4258, v4259, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2117 s i := by
  change (v4433 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v4298, v4299, v4412, v4413, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2117 s i := by
  change (v4587 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v4452, v4453, v4566, v4567, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2117 s i := by
  change (v4705 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v4598, v4684, v4685, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2117 s i := by
  change (v4823 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v4716, v4802, v4803, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2117 s i := by
  change (v4941 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v4834, v4920, v4921, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2117 s i := by
  change (v5059 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v4952, v5038, v5039, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2117 s i := by
  change (v5177 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v5070, v5156, v5157, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2117 s i := by
  change (v5295 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v5188, v5274, v5275, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2117 s i := by
  change (v5413 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v5306, v5392, v5393, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2117 s i := by
  change (v5531 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v5424, v5510, v5511, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2117 s i := by
  change (v5649 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v5542, v5628, v5629, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2117 s i := by
  change (v5767 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v5660, v5746, v5747, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2117 s i := by
  change (v5885 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v5778, v5864, v5865, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2117 s i := by
  change (v6003 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v5896, v5982, v5983, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2117 s i := by
  change (v6121 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v6014, v6100, v6101, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2117 s i := by
  change (v6239 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v6132, v6218, v6219, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2117 s i := by
  change (v6357 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v6250, v6336, v6337, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
private theorem reference_lhu_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2117 s i := by
  change (v6475 s i) = v2117 s i
  simp [v0, v1, ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1066 s i commit known, aligned, v6368, v6454, v6455, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, reset, target]
theorem reference_lhu_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2097 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2117 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x1 s i reset commit aligned known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x2 s i reset commit aligned known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x3 s i reset commit aligned known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x4 s i reset commit aligned known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x5 s i reset commit aligned known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x6 s i reset commit aligned known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x7 s i reset commit aligned known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x8 s i reset commit aligned known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x9 s i reset commit aligned known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x10 s i reset commit aligned known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x11 s i reset commit aligned known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x12 s i reset commit aligned known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x13 s i reset commit aligned known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x14 s i reset commit aligned known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x15 s i reset commit aligned known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x16 s i reset commit aligned known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x17 s i reset commit aligned known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x18 s i reset commit aligned known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x19 s i reset commit aligned known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x20 s i reset commit aligned known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x21 s i reset commit aligned known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x22 s i reset commit aligned known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x23 s i reset commit aligned known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x24 s i reset commit aligned known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x25 s i reset commit aligned known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x26 s i reset commit aligned known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x27 s i reset commit aligned known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x28 s i reset commit aligned known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x29 s i reset commit aligned known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x30 s i reset commit aligned known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_lhu_rd s i commit known).trans target
    rw [target]
    exact reference_lhu_next_x31 s i reset commit aligned known refTarget
#print axioms reference_lhu_written_value
end RiscvMiniProofs
