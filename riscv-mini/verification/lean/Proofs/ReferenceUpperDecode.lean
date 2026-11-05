import Proofs.ReferenceReads
import Proofs.UpperArithmetic
import Proofs.MaskFacts
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
private theorem reference_commit_instruction (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v977 s i = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by simp [v977, v975, v974, v973, commit]
private theorem ref_lui_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_lui_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_lui_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1122 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1122 s i = 0 := by
  change (if (1073762355 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1130 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1130 s i = 0 := by
  change (if (1073741875 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1138 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1138 s i = 0 := by
  change (if (20531 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1146 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1146 s i = 0 := by
  change (if (4147 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1154 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1154 s i = 0 := by
  change (if (16435 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1162 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1162 s i = 0 := by
  change (if (24627 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 4261441663 24627 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1170 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1170 s i = 0 := by
  change (if (28723 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 4261441663 28723 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1178 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1178 s i = 0 := by
  change (if (12339 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1186 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1186 s i = 0 := by
  change (if (8243 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1194 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1194 s i = 0 := by
  change (if (51 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1203 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1203 s i = 0 := by
  change (if (23 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1209 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1209 s i = 1 := by
  change (if (55 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 127 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_lui_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lui_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 55 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_lui_rd (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) :
    v1320 s i = BitVec.extractLsb' 7 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1046 s i commit known, ref_lui_v1052 s i commit known, ref_lui_v1058 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v1210, v1211, v1290, v1291, v1292, v1293, v1294, v1295, v1296, v1297, v1298, v1299, v1300, v1301, v1302, v1303, v1304, v1305, v1306, v1307, v1308, v1309, v1310, v1311, v1312, v1313, v1314, v1315, v1316, v1317, v1318, v1319, v1320, commit, reference_commit_instruction s i commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega, show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 25 by omega, show 7+j < 31 by omega, show 7+j < 32 by omega]
theorem reference_lui_immediate (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) : v2092 s i = immediateU s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_lui_v1046 s i commit known, ref_lui_v1052 s i commit known, ref_lui_v1058 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, ref_lui_v1333 s i commit known, ref_lui_v1339 s i commit known, ref_lui_v1345 s i commit known, ref_lui_v1351 s i commit known, ref_lui_v1358 s i commit known, ref_lui_v1365 s i commit known, ref_lui_v1372 s i commit known, ref_lui_v1379 s i commit known, ref_lui_v1386 s i commit known, v1810, v2029, v2030, v2031, v2032, v2034, v2071, v2072, v2073, v2074, v2075, v2076, v2077, v2078, v2079, v2080, v2081, v2082, v2083, v2084, v2085, v2086, v2087, v2088, v2089, v2090, v2091, v2092, commit, reference_commit_instruction s i commit, BitVec.reduceEq, if_true, if_false]
  rfl
theorem aligned_reference_arithmetic_lui (s : State) (i : Inputs)
    (aligned : DecodedAluAligned s) (_agree : RegisterAgreement s)
    (_zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2092 s i := by
  exact aligned.trans ((decoded_execution_lui _ _ _ _ known).trans
    (reference_lui_immediate s i commit known).symm)
#print axioms aligned_reference_arithmetic_lui
private theorem reference_lui_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2092 s i := by
  change (v2431 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v2310, v2311, v2370, v2371, v2373, v2375, v2377, v2379, v2381, v2383, v2385, v2387, v2389, v2391, v2393, v2396, v2399, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2092 s i := by
  change (v2585 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v2486, v2487, v2524, v2525, v2527, v2529, v2531, v2533, v2535, v2537, v2539, v2541, v2543, v2545, v2547, v2550, v2553, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2092 s i := by
  change (v2739 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v2640, v2641, v2678, v2679, v2681, v2683, v2685, v2687, v2689, v2691, v2693, v2695, v2697, v2699, v2701, v2704, v2707, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2092 s i := by
  change (v2893 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v2794, v2795, v2832, v2833, v2835, v2837, v2839, v2841, v2843, v2845, v2847, v2849, v2851, v2853, v2855, v2858, v2861, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2092 s i := by
  change (v3047 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v2948, v2949, v2986, v2987, v2989, v2991, v2993, v2995, v2997, v2999, v3001, v3003, v3005, v3007, v3009, v3012, v3015, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2092 s i := by
  change (v3201 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v3102, v3103, v3140, v3141, v3143, v3145, v3147, v3149, v3151, v3153, v3155, v3157, v3159, v3161, v3163, v3166, v3169, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2092 s i := by
  change (v3355 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v3256, v3257, v3294, v3295, v3297, v3299, v3301, v3303, v3305, v3307, v3309, v3311, v3313, v3315, v3317, v3320, v3323, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2092 s i := by
  change (v3509 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v3410, v3411, v3448, v3449, v3451, v3453, v3455, v3457, v3459, v3461, v3463, v3465, v3467, v3469, v3471, v3474, v3477, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2092 s i := by
  change (v3663 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v3564, v3565, v3602, v3603, v3605, v3607, v3609, v3611, v3613, v3615, v3617, v3619, v3621, v3623, v3625, v3628, v3631, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2092 s i := by
  change (v3817 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v3718, v3719, v3756, v3757, v3759, v3761, v3763, v3765, v3767, v3769, v3771, v3773, v3775, v3777, v3779, v3782, v3785, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2092 s i := by
  change (v3971 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v3872, v3873, v3910, v3911, v3913, v3915, v3917, v3919, v3921, v3923, v3925, v3927, v3929, v3931, v3933, v3936, v3939, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2092 s i := by
  change (v4125 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v4026, v4027, v4064, v4065, v4067, v4069, v4071, v4073, v4075, v4077, v4079, v4081, v4083, v4085, v4087, v4090, v4093, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2092 s i := by
  change (v4279 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v4180, v4181, v4218, v4219, v4221, v4223, v4225, v4227, v4229, v4231, v4233, v4235, v4237, v4239, v4241, v4244, v4247, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2092 s i := by
  change (v4433 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v4334, v4335, v4372, v4373, v4375, v4377, v4379, v4381, v4383, v4385, v4387, v4389, v4391, v4393, v4395, v4398, v4401, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2092 s i := by
  change (v4587 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v4488, v4489, v4526, v4527, v4529, v4531, v4533, v4535, v4537, v4539, v4541, v4543, v4545, v4547, v4549, v4552, v4555, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2092 s i := by
  change (v4705 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v4616, v4644, v4645, v4647, v4649, v4651, v4653, v4655, v4657, v4659, v4661, v4663, v4665, v4667, v4670, v4673, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2092 s i := by
  change (v4823 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v4734, v4762, v4763, v4765, v4767, v4769, v4771, v4773, v4775, v4777, v4779, v4781, v4783, v4785, v4788, v4791, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2092 s i := by
  change (v4941 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v4852, v4880, v4881, v4883, v4885, v4887, v4889, v4891, v4893, v4895, v4897, v4899, v4901, v4903, v4906, v4909, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2092 s i := by
  change (v5059 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v4970, v4998, v4999, v5001, v5003, v5005, v5007, v5009, v5011, v5013, v5015, v5017, v5019, v5021, v5024, v5027, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2092 s i := by
  change (v5177 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v5088, v5116, v5117, v5119, v5121, v5123, v5125, v5127, v5129, v5131, v5133, v5135, v5137, v5139, v5142, v5145, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2092 s i := by
  change (v5295 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v5206, v5234, v5235, v5237, v5239, v5241, v5243, v5245, v5247, v5249, v5251, v5253, v5255, v5257, v5260, v5263, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2092 s i := by
  change (v5413 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v5324, v5352, v5353, v5355, v5357, v5359, v5361, v5363, v5365, v5367, v5369, v5371, v5373, v5375, v5378, v5381, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2092 s i := by
  change (v5531 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v5442, v5470, v5471, v5473, v5475, v5477, v5479, v5481, v5483, v5485, v5487, v5489, v5491, v5493, v5496, v5499, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2092 s i := by
  change (v5649 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v5560, v5588, v5589, v5591, v5593, v5595, v5597, v5599, v5601, v5603, v5605, v5607, v5609, v5611, v5614, v5617, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2092 s i := by
  change (v5767 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v5678, v5706, v5707, v5709, v5711, v5713, v5715, v5717, v5719, v5721, v5723, v5725, v5727, v5729, v5732, v5735, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2092 s i := by
  change (v5885 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v5796, v5824, v5825, v5827, v5829, v5831, v5833, v5835, v5837, v5839, v5841, v5843, v5845, v5847, v5850, v5853, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2092 s i := by
  change (v6003 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v5914, v5942, v5943, v5945, v5947, v5949, v5951, v5953, v5955, v5957, v5959, v5961, v5963, v5965, v5968, v5971, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2092 s i := by
  change (v6121 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v6032, v6060, v6061, v6063, v6065, v6067, v6069, v6071, v6073, v6075, v6077, v6079, v6081, v6083, v6086, v6089, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2092 s i := by
  change (v6239 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v6150, v6178, v6179, v6181, v6183, v6185, v6187, v6189, v6191, v6193, v6195, v6197, v6199, v6201, v6204, v6207, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2092 s i := by
  change (v6357 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v6268, v6296, v6297, v6299, v6301, v6303, v6305, v6307, v6309, v6311, v6313, v6315, v6317, v6319, v6322, v6325, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
private theorem reference_lui_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2092 s i := by
  change (v6475 s i) = v2092 s i
  simp [v0, v1, ref_lui_v1005 s i commit known, ref_lui_v1013 s i commit known, ref_lui_v1021 s i commit known, ref_lui_v1029 s i commit known, ref_lui_v1037 s i commit known, ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, ref_lui_v1106 s i commit known, ref_lui_v1114 s i commit known, ref_lui_v1122 s i commit known, ref_lui_v1130 s i commit known, ref_lui_v1138 s i commit known, ref_lui_v1146 s i commit known, ref_lui_v1154 s i commit known, ref_lui_v1162 s i commit known, ref_lui_v1170 s i commit known, ref_lui_v1178 s i commit known, ref_lui_v1186 s i commit known, ref_lui_v1194 s i commit known, ref_lui_v1203 s i commit known, ref_lui_v1209 s i commit known, v6386, v6414, v6415, v6417, v6419, v6421, v6423, v6425, v6427, v6429, v6431, v6433, v6435, v6437, v6440, v6443, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_lui_v980 s i commit known, ref_lui_v989 s i commit known, ref_lui_v997 s i commit known, reset, target]
theorem reference_lui_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2092 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x1 s i reset commit known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x2 s i reset commit known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x3 s i reset commit known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x4 s i reset commit known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x5 s i reset commit known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x6 s i reset commit known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x7 s i reset commit known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x8 s i reset commit known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x9 s i reset commit known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x10 s i reset commit known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x11 s i reset commit known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x12 s i reset commit known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x13 s i reset commit known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x14 s i reset commit known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x15 s i reset commit known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x16 s i reset commit known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x17 s i reset commit known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x18 s i reset commit known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x19 s i reset commit known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x20 s i reset commit known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x21 s i reset commit known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x22 s i reset commit known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x23 s i reset commit known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x24 s i reset commit known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x25 s i reset commit known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x26 s i reset commit known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x27 s i reset commit known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x28 s i reset commit known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x29 s i reset commit known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x30 s i reset commit known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_lui_rd s i commit known).trans target
    rw [target]
    exact reference_lui_next_x31 s i reset commit known refTarget
#print axioms reference_lui_written_value
private theorem ref_auipc_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_auipc_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_auipc_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1122 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1122 s i = 0 := by
  change (if (1073762355 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1130 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1130 s i = 0 := by
  change (if (1073741875 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1138 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1138 s i = 0 := by
  change (if (20531 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1146 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1146 s i = 0 := by
  change (if (4147 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1154 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1154 s i = 0 := by
  change (if (16435 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1162 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1162 s i = 0 := by
  change (if (24627 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 4261441663 24627 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1170 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1170 s i = 0 := by
  change (if (28723 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 4261441663 28723 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1178 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1178 s i = 0 := by
  change (if (12339 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1186 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1186 s i = 0 := by
  change (if (8243 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1194 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1194 s i = 0 := by
  change (if (51 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1203 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1203 s i = 1 := by
  change (if (23 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 127 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_auipc_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_auipc_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 127 23 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_auipc_rd (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) :
    v1320 s i = BitVec.extractLsb' 7 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1046 s i commit known, ref_auipc_v1052 s i commit known, ref_auipc_v1058 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v1204, v1205, v1291, v1292, v1293, v1294, v1295, v1296, v1297, v1298, v1299, v1300, v1301, v1302, v1303, v1304, v1305, v1306, v1307, v1308, v1309, v1310, v1311, v1312, v1313, v1314, v1315, v1316, v1317, v1318, v1319, v1320, commit, reference_commit_instruction s i commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega, show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 25 by omega, show 7+j < 31 by omega, show 7+j < 32 by omega]
theorem reference_auipc_immediate (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) : v2092 s i = immediateU s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_auipc_v1046 s i commit known, ref_auipc_v1052 s i commit known, ref_auipc_v1058 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1203 s i commit known, ref_auipc_v1333 s i commit known, ref_auipc_v1339 s i commit known, ref_auipc_v1345 s i commit known, ref_auipc_v1351 s i commit known, ref_auipc_v1358 s i commit known, ref_auipc_v1365 s i commit known, ref_auipc_v1372 s i commit known, ref_auipc_v1379 s i commit known, ref_auipc_v1386 s i commit known, v1810, v2028, v2031, v2032, v2033, v2072, v2073, v2074, v2075, v2076, v2077, v2078, v2079, v2080, v2081, v2082, v2083, v2084, v2085, v2086, v2087, v2088, v2089, v2090, v2091, v2092, commit, reference_commit_instruction s i commit, BitVec.reduceEq, if_true, if_false]
  rfl
theorem aligned_reference_arithmetic_auipc (s : State) (i : Inputs)
    (aligned : DecodedAluAligned s) (_agree : RegisterAgreement s)
    (_zero : ReferenceZero s) (commit : v964 s i = 1)
    (pc : WritebackPcAgreement s)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2309 s i := by
  have value := aligned.trans (decoded_execution_auipc _ _ _ _ known)
  have pcEq : s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc = v2222 s i := pc
  rw [← reference_auipc_immediate s i commit known, pcEq] at value
  exact value.trans (reference_auipc_value s i).symm
#print axioms aligned_reference_arithmetic_auipc
private theorem reference_auipc_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2309 s i := by
  change (v2431 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v2304, v2305, v2372, v2373, v2375, v2377, v2379, v2381, v2383, v2385, v2387, v2389, v2391, v2393, v2396, v2399, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2309 s i := by
  change (v2585 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v2484, v2485, v2526, v2527, v2529, v2531, v2533, v2535, v2537, v2539, v2541, v2543, v2545, v2547, v2550, v2553, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2309 s i := by
  change (v2739 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v2638, v2639, v2680, v2681, v2683, v2685, v2687, v2689, v2691, v2693, v2695, v2697, v2699, v2701, v2704, v2707, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2309 s i := by
  change (v2893 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v2792, v2793, v2834, v2835, v2837, v2839, v2841, v2843, v2845, v2847, v2849, v2851, v2853, v2855, v2858, v2861, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2309 s i := by
  change (v3047 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v2946, v2947, v2988, v2989, v2991, v2993, v2995, v2997, v2999, v3001, v3003, v3005, v3007, v3009, v3012, v3015, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2309 s i := by
  change (v3201 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v3100, v3101, v3142, v3143, v3145, v3147, v3149, v3151, v3153, v3155, v3157, v3159, v3161, v3163, v3166, v3169, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2309 s i := by
  change (v3355 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v3254, v3255, v3296, v3297, v3299, v3301, v3303, v3305, v3307, v3309, v3311, v3313, v3315, v3317, v3320, v3323, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2309 s i := by
  change (v3509 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v3408, v3409, v3450, v3451, v3453, v3455, v3457, v3459, v3461, v3463, v3465, v3467, v3469, v3471, v3474, v3477, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2309 s i := by
  change (v3663 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v3562, v3563, v3604, v3605, v3607, v3609, v3611, v3613, v3615, v3617, v3619, v3621, v3623, v3625, v3628, v3631, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2309 s i := by
  change (v3817 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v3716, v3717, v3758, v3759, v3761, v3763, v3765, v3767, v3769, v3771, v3773, v3775, v3777, v3779, v3782, v3785, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2309 s i := by
  change (v3971 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v3870, v3871, v3912, v3913, v3915, v3917, v3919, v3921, v3923, v3925, v3927, v3929, v3931, v3933, v3936, v3939, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2309 s i := by
  change (v4125 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v4024, v4025, v4066, v4067, v4069, v4071, v4073, v4075, v4077, v4079, v4081, v4083, v4085, v4087, v4090, v4093, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2309 s i := by
  change (v4279 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v4178, v4179, v4220, v4221, v4223, v4225, v4227, v4229, v4231, v4233, v4235, v4237, v4239, v4241, v4244, v4247, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2309 s i := by
  change (v4433 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v4332, v4333, v4374, v4375, v4377, v4379, v4381, v4383, v4385, v4387, v4389, v4391, v4393, v4395, v4398, v4401, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2309 s i := by
  change (v4587 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v4486, v4487, v4528, v4529, v4531, v4533, v4535, v4537, v4539, v4541, v4543, v4545, v4547, v4549, v4552, v4555, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2309 s i := by
  change (v4705 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v4615, v4646, v4647, v4649, v4651, v4653, v4655, v4657, v4659, v4661, v4663, v4665, v4667, v4670, v4673, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2309 s i := by
  change (v4823 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v4733, v4764, v4765, v4767, v4769, v4771, v4773, v4775, v4777, v4779, v4781, v4783, v4785, v4788, v4791, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2309 s i := by
  change (v4941 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v4851, v4882, v4883, v4885, v4887, v4889, v4891, v4893, v4895, v4897, v4899, v4901, v4903, v4906, v4909, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2309 s i := by
  change (v5059 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v4969, v5000, v5001, v5003, v5005, v5007, v5009, v5011, v5013, v5015, v5017, v5019, v5021, v5024, v5027, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2309 s i := by
  change (v5177 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v5087, v5118, v5119, v5121, v5123, v5125, v5127, v5129, v5131, v5133, v5135, v5137, v5139, v5142, v5145, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2309 s i := by
  change (v5295 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v5205, v5236, v5237, v5239, v5241, v5243, v5245, v5247, v5249, v5251, v5253, v5255, v5257, v5260, v5263, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2309 s i := by
  change (v5413 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v5323, v5354, v5355, v5357, v5359, v5361, v5363, v5365, v5367, v5369, v5371, v5373, v5375, v5378, v5381, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2309 s i := by
  change (v5531 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v5441, v5472, v5473, v5475, v5477, v5479, v5481, v5483, v5485, v5487, v5489, v5491, v5493, v5496, v5499, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2309 s i := by
  change (v5649 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v5559, v5590, v5591, v5593, v5595, v5597, v5599, v5601, v5603, v5605, v5607, v5609, v5611, v5614, v5617, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2309 s i := by
  change (v5767 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v5677, v5708, v5709, v5711, v5713, v5715, v5717, v5719, v5721, v5723, v5725, v5727, v5729, v5732, v5735, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2309 s i := by
  change (v5885 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v5795, v5826, v5827, v5829, v5831, v5833, v5835, v5837, v5839, v5841, v5843, v5845, v5847, v5850, v5853, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2309 s i := by
  change (v6003 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v5913, v5944, v5945, v5947, v5949, v5951, v5953, v5955, v5957, v5959, v5961, v5963, v5965, v5968, v5971, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2309 s i := by
  change (v6121 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v6031, v6062, v6063, v6065, v6067, v6069, v6071, v6073, v6075, v6077, v6079, v6081, v6083, v6086, v6089, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2309 s i := by
  change (v6239 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v6149, v6180, v6181, v6183, v6185, v6187, v6189, v6191, v6193, v6195, v6197, v6199, v6201, v6204, v6207, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2309 s i := by
  change (v6357 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v6267, v6298, v6299, v6301, v6303, v6305, v6307, v6309, v6311, v6313, v6315, v6317, v6319, v6322, v6325, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
private theorem reference_auipc_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2309 s i := by
  change (v6475 s i) = v2309 s i
  simp [v0, v1, ref_auipc_v1005 s i commit known, ref_auipc_v1013 s i commit known, ref_auipc_v1021 s i commit known, ref_auipc_v1029 s i commit known, ref_auipc_v1037 s i commit known, ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, ref_auipc_v1106 s i commit known, ref_auipc_v1114 s i commit known, ref_auipc_v1122 s i commit known, ref_auipc_v1130 s i commit known, ref_auipc_v1138 s i commit known, ref_auipc_v1146 s i commit known, ref_auipc_v1154 s i commit known, ref_auipc_v1162 s i commit known, ref_auipc_v1170 s i commit known, ref_auipc_v1178 s i commit known, ref_auipc_v1186 s i commit known, ref_auipc_v1194 s i commit known, ref_auipc_v1203 s i commit known, v6385, v6416, v6417, v6419, v6421, v6423, v6425, v6427, v6429, v6431, v6433, v6435, v6437, v6440, v6443, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_auipc_v980 s i commit known, ref_auipc_v989 s i commit known, ref_auipc_v997 s i commit known, reset, target]
theorem reference_auipc_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2309 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x1 s i reset commit known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x2 s i reset commit known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x3 s i reset commit known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x4 s i reset commit known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x5 s i reset commit known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x6 s i reset commit known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x7 s i reset commit known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x8 s i reset commit known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x9 s i reset commit known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x10 s i reset commit known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x11 s i reset commit known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x12 s i reset commit known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x13 s i reset commit known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x14 s i reset commit known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x15 s i reset commit known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x16 s i reset commit known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x17 s i reset commit known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x18 s i reset commit known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x19 s i reset commit known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x20 s i reset commit known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x21 s i reset commit known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x22 s i reset commit known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x23 s i reset commit known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x24 s i reset commit known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x25 s i reset commit known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x26 s i reset commit known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x27 s i reset commit known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x28 s i reset commit known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x29 s i reset commit known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x30 s i reset commit known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_auipc_rd s i commit known).trans target
    rw [target]
    exact reference_auipc_next_x31 s i reset commit known refTarget
#print axioms reference_auipc_written_value
end RiscvMiniProofs
