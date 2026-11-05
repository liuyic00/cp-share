import Proofs.ReferenceReads
import Proofs.ReferenceJump
import Proofs.ImmediateFacts
import Proofs.JumpImmediate
import Proofs.MaskFacts
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
private theorem reference_commit_instruction (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v977 s i = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by simp [v977, v975, v974, v973, commit]
private theorem ref_jal_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jal_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jal_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jal_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jal_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jal_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jal_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_jal_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_jal_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jal_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jal_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jal_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jal_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jal_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jal_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1114 s i = 1 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 127 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_jal_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jal_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jal_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jal_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jal_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jal_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jal_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jal_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jal_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jal_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jal_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jal_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 111 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_jal_rd (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) :
    v1320 s i = BitVec.extractLsb' 7 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1046 s i commit known, ref_jal_v1052 s i commit known, ref_jal_v1058 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, v1115, v1116, v1117, v1118, v1119, v1302, v1303, v1304, v1305, v1306, v1307, v1308, v1309, v1310, v1311, v1312, v1313, v1314, v1315, v1316, v1317, v1318, v1319, v1320, commit, reference_commit_instruction s i commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega, show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 25 by omega, show 7+j < 31 by omega, show 7+j < 32 by omega]
theorem reference_jal_immediate (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) : v2092 s i = immediateJ s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_jal_v1046 s i commit known, ref_jal_v1052 s i commit known, ref_jal_v1058 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, v1115, v1116, v1117, ref_jal_v1333 s i commit known, ref_jal_v1339 s i commit known, ref_jal_v1345 s i commit known, ref_jal_v1351 s i commit known, ref_jal_v1358 s i commit known, ref_jal_v1365 s i commit known, ref_jal_v1372 s i commit known, ref_jal_v1379 s i commit known, ref_jal_v1386 s i commit known, v1925, v1926, v1927, v1928, v1929, v1930, v1931, v1932, v1933, v2008, v2009, v2010, v2011, v2013, v2014, v2015, v2016, v2017, v2019, v2020, v2021, v2022, v2023, v2024, v2025, v2026, v2027, v2073, v2074, v2075, v2076, v2077, v2078, v2079, v2080, v2081, v2082, v2083, v2084, v2085, v2086, v2087, v2088, v2089, v2090, v2091, v2092, v4, commit, reference_commit_instruction s i commit, BitVec.reduceEq, if_true, if_false]
  rw [jump_sign_conditional]
  simp [immediateJ, jumpBits, extract_prefix]
private theorem reference_jal_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2255 s i := by
  change (v2431 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v2250, v2251, v2394, v2395, v2396, v2399, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2255 s i := by
  change (v2585 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v2462, v2463, v2548, v2549, v2550, v2553, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2255 s i := by
  change (v2739 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v2616, v2617, v2702, v2703, v2704, v2707, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2255 s i := by
  change (v2893 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v2770, v2771, v2856, v2857, v2858, v2861, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2255 s i := by
  change (v3047 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v2924, v2925, v3010, v3011, v3012, v3015, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2255 s i := by
  change (v3201 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v3078, v3079, v3164, v3165, v3166, v3169, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2255 s i := by
  change (v3355 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v3232, v3233, v3318, v3319, v3320, v3323, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2255 s i := by
  change (v3509 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v3386, v3387, v3472, v3473, v3474, v3477, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2255 s i := by
  change (v3663 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v3540, v3541, v3626, v3627, v3628, v3631, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2255 s i := by
  change (v3817 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v3694, v3695, v3780, v3781, v3782, v3785, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2255 s i := by
  change (v3971 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v3848, v3849, v3934, v3935, v3936, v3939, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2255 s i := by
  change (v4125 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v4002, v4003, v4088, v4089, v4090, v4093, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2255 s i := by
  change (v4279 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v4156, v4157, v4242, v4243, v4244, v4247, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2255 s i := by
  change (v4433 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v4310, v4311, v4396, v4397, v4398, v4401, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2255 s i := by
  change (v4587 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v4464, v4465, v4550, v4551, v4552, v4555, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2255 s i := by
  change (v4705 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v4604, v4668, v4669, v4670, v4673, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2255 s i := by
  change (v4823 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v4722, v4786, v4787, v4788, v4791, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2255 s i := by
  change (v4941 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v4840, v4904, v4905, v4906, v4909, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2255 s i := by
  change (v5059 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v4958, v5022, v5023, v5024, v5027, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2255 s i := by
  change (v5177 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v5076, v5140, v5141, v5142, v5145, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2255 s i := by
  change (v5295 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v5194, v5258, v5259, v5260, v5263, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2255 s i := by
  change (v5413 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v5312, v5376, v5377, v5378, v5381, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2255 s i := by
  change (v5531 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v5430, v5494, v5495, v5496, v5499, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2255 s i := by
  change (v5649 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v5548, v5612, v5613, v5614, v5617, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2255 s i := by
  change (v5767 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v5666, v5730, v5731, v5732, v5735, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2255 s i := by
  change (v5885 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v5784, v5848, v5849, v5850, v5853, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2255 s i := by
  change (v6003 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v5902, v5966, v5967, v5968, v5971, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2255 s i := by
  change (v6121 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v6020, v6084, v6085, v6086, v6089, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2255 s i := by
  change (v6239 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v6138, v6202, v6203, v6204, v6207, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2255 s i := by
  change (v6357 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v6256, v6320, v6321, v6322, v6325, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
private theorem reference_jal_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2255 s i := by
  change (v6475 s i) = v2255 s i
  simp [v0, v1, ref_jal_v1005 s i commit known, ref_jal_v1013 s i commit known, ref_jal_v1021 s i commit known, ref_jal_v1029 s i commit known, ref_jal_v1037 s i commit known, ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, ref_jal_v1106 s i commit known, ref_jal_v1114 s i commit known, aligned, v6374, v6438, v6439, v6440, v6443, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_jal_v980 s i commit known, ref_jal_v989 s i commit known, ref_jal_v997 s i commit known, reset, target]
theorem reference_jal_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2249 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2255 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x1 s i reset commit aligned known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x2 s i reset commit aligned known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x3 s i reset commit aligned known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x4 s i reset commit aligned known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x5 s i reset commit aligned known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x6 s i reset commit aligned known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x7 s i reset commit aligned known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x8 s i reset commit aligned known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x9 s i reset commit aligned known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x10 s i reset commit aligned known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x11 s i reset commit aligned known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x12 s i reset commit aligned known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x13 s i reset commit aligned known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x14 s i reset commit aligned known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x15 s i reset commit aligned known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x16 s i reset commit aligned known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x17 s i reset commit aligned known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x18 s i reset commit aligned known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x19 s i reset commit aligned known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x20 s i reset commit aligned known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x21 s i reset commit aligned known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x22 s i reset commit aligned known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x23 s i reset commit aligned known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x24 s i reset commit aligned known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x25 s i reset commit aligned known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x26 s i reset commit aligned known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x27 s i reset commit aligned known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x28 s i reset commit aligned known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x29 s i reset commit aligned known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x30 s i reset commit aligned known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_jal_rd s i commit known).trans target
    rw [target]
    exact reference_jal_next_x31 s i reset commit aligned known refTarget
#print axioms reference_jal_written_value
private theorem ref_jalr_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jalr_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jalr_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jalr_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jalr_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jalr_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jalr_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_jalr_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_jalr_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jalr_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jalr_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jalr_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jalr_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jalr_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v1106 s i = 1 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_jalr_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jalr_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jalr_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jalr_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jalr_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jalr_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jalr_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jalr_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jalr_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jalr_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jalr_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_jalr_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 103 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_jalr_rd (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) :
    v1320 s i = BitVec.extractLsb' 7 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1046 s i commit known, ref_jalr_v1052 s i commit known, ref_jalr_v1058 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, v1107, v1108, v1109, v1110, v1303, v1304, v1305, v1306, v1307, v1308, v1309, v1310, v1311, v1312, v1313, v1314, v1315, v1316, v1317, v1318, v1319, v1320, commit, reference_commit_instruction s i commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega, show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 25 by omega, show 7+j < 31 by omega, show 7+j < 32 by omega]
theorem reference_jalr_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1046 s i commit known, ref_jalr_v1052 s i commit known, ref_jalr_v1058 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, v1107, ref_jalr_v1333 s i commit known, ref_jalr_v1339 s i commit known, ref_jalr_v1345 s i commit known, ref_jalr_v1351 s i commit known, ref_jalr_v1358 s i commit known, ref_jalr_v1365 s i commit known, ref_jalr_v1372 s i commit known, ref_jalr_v1379 s i commit known, ref_jalr_v1386 s i commit known, v1575, v1614, v1615, v1616, v1617, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_jalr_immediate (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) : v2092 s i = immediateI s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_jalr_v1046 s i commit known, ref_jalr_v1052 s i commit known, ref_jalr_v1058 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, ref_jalr_v1333 s i commit known, ref_jalr_v1339 s i commit known, ref_jalr_v1345 s i commit known, ref_jalr_v1351 s i commit known, ref_jalr_v1358 s i commit known, ref_jalr_v1365 s i commit known, ref_jalr_v1372 s i commit known, ref_jalr_v1379 s i commit known, ref_jalr_v1386 s i commit known, v1800, v1820, v1821, v1822, v1823, v1824, v1825, v1826, v1827, v1828, v1829, v1831, v1832, v2005, v2006, v2007, v2074, v2075, v2076, v2077, v2078, v2079, v2080, v2081, v2082, v2083, v2084, v2085, v2086, v2087, v2088, v2089, v2090, v2091, v2092, commit, reference_commit_instruction s i commit, BitVec.reduceEq, if_true, if_false]
  rw [reference_sign_extension]
  rfl
theorem reference_jalr_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_jalr_rs1 s i commit known]
private theorem reference_jalr_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2226 s i := by
  change (v2431 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v2220, v2221, v2397, v2398, v2399, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2226 s i := by
  change (v2585 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v2460, v2461, v2551, v2552, v2553, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2226 s i := by
  change (v2739 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v2614, v2615, v2705, v2706, v2707, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2226 s i := by
  change (v2893 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v2768, v2769, v2859, v2860, v2861, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2226 s i := by
  change (v3047 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v2922, v2923, v3013, v3014, v3015, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2226 s i := by
  change (v3201 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v3076, v3077, v3167, v3168, v3169, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2226 s i := by
  change (v3355 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v3230, v3231, v3321, v3322, v3323, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2226 s i := by
  change (v3509 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v3384, v3385, v3475, v3476, v3477, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2226 s i := by
  change (v3663 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v3538, v3539, v3629, v3630, v3631, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2226 s i := by
  change (v3817 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v3692, v3693, v3783, v3784, v3785, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2226 s i := by
  change (v3971 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v3846, v3847, v3937, v3938, v3939, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2226 s i := by
  change (v4125 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v4000, v4001, v4091, v4092, v4093, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2226 s i := by
  change (v4279 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v4154, v4155, v4245, v4246, v4247, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2226 s i := by
  change (v4433 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v4308, v4309, v4399, v4400, v4401, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2226 s i := by
  change (v4587 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v4462, v4463, v4553, v4554, v4555, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2226 s i := by
  change (v4705 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v4603, v4671, v4672, v4673, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2226 s i := by
  change (v4823 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v4721, v4789, v4790, v4791, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2226 s i := by
  change (v4941 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v4839, v4907, v4908, v4909, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2226 s i := by
  change (v5059 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v4957, v5025, v5026, v5027, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2226 s i := by
  change (v5177 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v5075, v5143, v5144, v5145, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2226 s i := by
  change (v5295 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v5193, v5261, v5262, v5263, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2226 s i := by
  change (v5413 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v5311, v5379, v5380, v5381, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2226 s i := by
  change (v5531 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v5429, v5497, v5498, v5499, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2226 s i := by
  change (v5649 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v5547, v5615, v5616, v5617, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2226 s i := by
  change (v5767 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v5665, v5733, v5734, v5735, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2226 s i := by
  change (v5885 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v5783, v5851, v5852, v5853, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2226 s i := by
  change (v6003 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v5901, v5969, v5970, v5971, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2226 s i := by
  change (v6121 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v6019, v6087, v6088, v6089, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2226 s i := by
  change (v6239 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v6137, v6205, v6206, v6207, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2226 s i := by
  change (v6357 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v6255, v6323, v6324, v6325, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
private theorem reference_jalr_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2226 s i := by
  change (v6475 s i) = v2226 s i
  simp [v0, v1, ref_jalr_v1005 s i commit known, ref_jalr_v1013 s i commit known, ref_jalr_v1021 s i commit known, ref_jalr_v1029 s i commit known, ref_jalr_v1037 s i commit known, ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, ref_jalr_v1106 s i commit known, aligned, v6373, v6441, v6442, v6443, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_jalr_v980 s i commit known, ref_jalr_v989 s i commit known, ref_jalr_v997 s i commit known, reset, target]
theorem reference_jalr_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v2219 s i = 1#1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2226 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x1 s i reset commit aligned known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x2 s i reset commit aligned known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x3 s i reset commit aligned known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x4 s i reset commit aligned known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x5 s i reset commit aligned known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x6 s i reset commit aligned known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x7 s i reset commit aligned known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x8 s i reset commit aligned known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x9 s i reset commit aligned known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x10 s i reset commit aligned known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x11 s i reset commit aligned known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x12 s i reset commit aligned known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x13 s i reset commit aligned known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x14 s i reset commit aligned known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x15 s i reset commit aligned known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x16 s i reset commit aligned known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x17 s i reset commit aligned known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x18 s i reset commit aligned known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x19 s i reset commit aligned known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x20 s i reset commit aligned known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x21 s i reset commit aligned known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x22 s i reset commit aligned known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x23 s i reset commit aligned known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x24 s i reset commit aligned known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x25 s i reset commit aligned known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x26 s i reset commit aligned known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x27 s i reset commit aligned known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x28 s i reset commit aligned known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x29 s i reset commit aligned known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x30 s i reset commit aligned known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_jalr_rd s i commit known).trans target
    rw [target]
    exact reference_jalr_next_x31 s i reset commit aligned known refTarget
#print axioms reference_jalr_written_value
end RiscvMiniProofs
