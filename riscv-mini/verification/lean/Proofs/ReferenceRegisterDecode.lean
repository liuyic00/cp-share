import Proofs.ReferenceReads
import Proofs.ReferenceExecution
import Proofs.MaskFacts
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
private theorem reference_commit_instruction (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v977 s i = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by simp [v977, v975, v974, v973, commit]
private theorem ref_add_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_add_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_add_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1122 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1122 s i = 0 := by
  change (if (1073762355 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1130 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1130 s i = 0 := by
  change (if (1073741875 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1138 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1138 s i = 0 := by
  change (if (20531 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1146 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1146 s i = 0 := by
  change (if (4147 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1154 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1154 s i = 0 := by
  change (if (16435 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1162 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1162 s i = 0 := by
  change (if (24627 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 4261441663 24627 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1170 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1170 s i = 0 := by
  change (if (28723 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 4261441663 28723 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1178 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1178 s i = 0 := by
  change (if (12339 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1186 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1186 s i = 0 := by
  change (if (8243 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1194 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1194 s i = 1 := by
  change (if (51 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 4261441663 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_add_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_add_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 51 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_add_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1046 s i commit known, ref_add_v1052 s i commit known, ref_add_v1058 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v1195, v1196, ref_add_v1333 s i commit known, ref_add_v1339 s i commit known, ref_add_v1345 s i commit known, ref_add_v1351 s i commit known, ref_add_v1358 s i commit known, ref_add_v1365 s i commit known, ref_add_v1372 s i commit known, ref_add_v1379 s i commit known, ref_add_v1386 s i commit known, v1585, v1604, v1605, v1606, v1607, v1608, v1609, v1610, v1611, v1612, v1613, v1614, v1615, v1616, v1617, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_add_rs2 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) :
    v1427 s i = BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v1195, ref_add_v1333 s i commit known, ref_add_v1339 s i commit known, ref_add_v1345 s i commit known, ref_add_v1351 s i commit known, ref_add_v1358 s i commit known, ref_add_v1365 s i commit known, ref_add_v1372 s i commit known, ref_add_v1379 s i commit known, ref_add_v1386 s i commit known, v1399, v1400, v1401, v1402, v1403, v1404, v1405, v1406, v1407, v1408, v1409, v1410, v1411, v1412, v1413, v1414, v1415, v1416, v1417, v1418, v1419, v1420, v1421, v1422, v1423, v1424, v1425, v1426, v1427, commit, reference_commit_instruction s i commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 20+j < 25 by omega, show 20+j < 31 by omega, show 20+j < 32 by omega]
theorem reference_add_rd (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) :
    v1320 s i = BitVec.extractLsb' 7 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1046 s i commit known, ref_add_v1052 s i commit known, ref_add_v1058 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v1195, v1196, v1197, v1198, v1199, v1292, v1293, v1294, v1295, v1296, v1297, v1298, v1299, v1300, v1301, v1302, v1303, v1304, v1305, v1306, v1307, v1308, v1309, v1310, v1311, v1312, v1313, v1314, v1315, v1316, v1317, v1318, v1319, v1320, commit, reference_commit_instruction s i commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega, show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 25 by omega, show 7+j < 31 by omega, show 7+j < 32 by omega]
theorem reference_add_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_add_rs1 s i commit known]
theorem reference_add_operand2 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) :
    v1539 s i = referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port2 s i zero, reference_add_rs2 s i commit known]
theorem aligned_reference_arithmetic_add (s : State) (i : Inputs)
    (aligned : DecodedAluAligned s) (agree : RegisterAgreement s)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2303 s i := by
  have arithmetic := decoded_reference_arithmetic_add s i s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
    s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc known
  rw [reference_add_operand1 s i zero commit known,
    reference_add_operand2 s i zero commit known] at arithmetic
  exact (decoded_alu_reference_operands s aligned agree).trans arithmetic
#print axioms aligned_reference_arithmetic_add
private theorem reference_add_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2303 s i := by
  change (v2431 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v2298, v2299, v2374, v2375, v2377, v2379, v2381, v2383, v2385, v2387, v2389, v2391, v2393, v2396, v2399, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2303 s i := by
  change (v2585 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v2482, v2483, v2528, v2529, v2531, v2533, v2535, v2537, v2539, v2541, v2543, v2545, v2547, v2550, v2553, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2303 s i := by
  change (v2739 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v2636, v2637, v2682, v2683, v2685, v2687, v2689, v2691, v2693, v2695, v2697, v2699, v2701, v2704, v2707, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2303 s i := by
  change (v2893 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v2790, v2791, v2836, v2837, v2839, v2841, v2843, v2845, v2847, v2849, v2851, v2853, v2855, v2858, v2861, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2303 s i := by
  change (v3047 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v2944, v2945, v2990, v2991, v2993, v2995, v2997, v2999, v3001, v3003, v3005, v3007, v3009, v3012, v3015, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2303 s i := by
  change (v3201 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v3098, v3099, v3144, v3145, v3147, v3149, v3151, v3153, v3155, v3157, v3159, v3161, v3163, v3166, v3169, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2303 s i := by
  change (v3355 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v3252, v3253, v3298, v3299, v3301, v3303, v3305, v3307, v3309, v3311, v3313, v3315, v3317, v3320, v3323, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2303 s i := by
  change (v3509 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v3406, v3407, v3452, v3453, v3455, v3457, v3459, v3461, v3463, v3465, v3467, v3469, v3471, v3474, v3477, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2303 s i := by
  change (v3663 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v3560, v3561, v3606, v3607, v3609, v3611, v3613, v3615, v3617, v3619, v3621, v3623, v3625, v3628, v3631, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2303 s i := by
  change (v3817 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v3714, v3715, v3760, v3761, v3763, v3765, v3767, v3769, v3771, v3773, v3775, v3777, v3779, v3782, v3785, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2303 s i := by
  change (v3971 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v3868, v3869, v3914, v3915, v3917, v3919, v3921, v3923, v3925, v3927, v3929, v3931, v3933, v3936, v3939, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2303 s i := by
  change (v4125 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v4022, v4023, v4068, v4069, v4071, v4073, v4075, v4077, v4079, v4081, v4083, v4085, v4087, v4090, v4093, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2303 s i := by
  change (v4279 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v4176, v4177, v4222, v4223, v4225, v4227, v4229, v4231, v4233, v4235, v4237, v4239, v4241, v4244, v4247, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2303 s i := by
  change (v4433 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v4330, v4331, v4376, v4377, v4379, v4381, v4383, v4385, v4387, v4389, v4391, v4393, v4395, v4398, v4401, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2303 s i := by
  change (v4587 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v4484, v4485, v4530, v4531, v4533, v4535, v4537, v4539, v4541, v4543, v4545, v4547, v4549, v4552, v4555, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2303 s i := by
  change (v4705 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v4614, v4648, v4649, v4651, v4653, v4655, v4657, v4659, v4661, v4663, v4665, v4667, v4670, v4673, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2303 s i := by
  change (v4823 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v4732, v4766, v4767, v4769, v4771, v4773, v4775, v4777, v4779, v4781, v4783, v4785, v4788, v4791, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2303 s i := by
  change (v4941 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v4850, v4884, v4885, v4887, v4889, v4891, v4893, v4895, v4897, v4899, v4901, v4903, v4906, v4909, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2303 s i := by
  change (v5059 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v4968, v5002, v5003, v5005, v5007, v5009, v5011, v5013, v5015, v5017, v5019, v5021, v5024, v5027, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2303 s i := by
  change (v5177 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v5086, v5120, v5121, v5123, v5125, v5127, v5129, v5131, v5133, v5135, v5137, v5139, v5142, v5145, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2303 s i := by
  change (v5295 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v5204, v5238, v5239, v5241, v5243, v5245, v5247, v5249, v5251, v5253, v5255, v5257, v5260, v5263, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2303 s i := by
  change (v5413 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v5322, v5356, v5357, v5359, v5361, v5363, v5365, v5367, v5369, v5371, v5373, v5375, v5378, v5381, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2303 s i := by
  change (v5531 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v5440, v5474, v5475, v5477, v5479, v5481, v5483, v5485, v5487, v5489, v5491, v5493, v5496, v5499, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2303 s i := by
  change (v5649 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v5558, v5592, v5593, v5595, v5597, v5599, v5601, v5603, v5605, v5607, v5609, v5611, v5614, v5617, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2303 s i := by
  change (v5767 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v5676, v5710, v5711, v5713, v5715, v5717, v5719, v5721, v5723, v5725, v5727, v5729, v5732, v5735, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2303 s i := by
  change (v5885 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v5794, v5828, v5829, v5831, v5833, v5835, v5837, v5839, v5841, v5843, v5845, v5847, v5850, v5853, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2303 s i := by
  change (v6003 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v5912, v5946, v5947, v5949, v5951, v5953, v5955, v5957, v5959, v5961, v5963, v5965, v5968, v5971, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2303 s i := by
  change (v6121 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v6030, v6064, v6065, v6067, v6069, v6071, v6073, v6075, v6077, v6079, v6081, v6083, v6086, v6089, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2303 s i := by
  change (v6239 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v6148, v6182, v6183, v6185, v6187, v6189, v6191, v6193, v6195, v6197, v6199, v6201, v6204, v6207, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2303 s i := by
  change (v6357 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v6266, v6300, v6301, v6303, v6305, v6307, v6309, v6311, v6313, v6315, v6317, v6319, v6322, v6325, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
private theorem reference_add_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2303 s i := by
  change (v6475 s i) = v2303 s i
  simp [v0, v1, ref_add_v1005 s i commit known, ref_add_v1013 s i commit known, ref_add_v1021 s i commit known, ref_add_v1029 s i commit known, ref_add_v1037 s i commit known, ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, ref_add_v1106 s i commit known, ref_add_v1114 s i commit known, ref_add_v1122 s i commit known, ref_add_v1130 s i commit known, ref_add_v1138 s i commit known, ref_add_v1146 s i commit known, ref_add_v1154 s i commit known, ref_add_v1162 s i commit known, ref_add_v1170 s i commit known, ref_add_v1178 s i commit known, ref_add_v1186 s i commit known, ref_add_v1194 s i commit known, v6384, v6418, v6419, v6421, v6423, v6425, v6427, v6429, v6431, v6433, v6435, v6437, v6440, v6443, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_add_v980 s i commit known, ref_add_v989 s i commit known, ref_add_v997 s i commit known, reset, target]
theorem reference_add_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2303 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x1 s i reset commit known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x2 s i reset commit known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x3 s i reset commit known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x4 s i reset commit known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x5 s i reset commit known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x6 s i reset commit known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x7 s i reset commit known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x8 s i reset commit known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x9 s i reset commit known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x10 s i reset commit known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x11 s i reset commit known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x12 s i reset commit known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x13 s i reset commit known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x14 s i reset commit known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x15 s i reset commit known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x16 s i reset commit known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x17 s i reset commit known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x18 s i reset commit known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x19 s i reset commit known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x20 s i reset commit known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x21 s i reset commit known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x22 s i reset commit known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x23 s i reset commit known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x24 s i reset commit known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x25 s i reset commit known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x26 s i reset commit known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x27 s i reset commit known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x28 s i reset commit known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x29 s i reset commit known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x30 s i reset commit known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_add_rd s i commit known).trans target
    rw [target]
    exact reference_add_next_x31 s i reset commit known refTarget
#print axioms reference_add_written_value
private theorem ref_sub_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_sub_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_sub_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v1122 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1122 s i = 0 := by
  change (if (1073762355 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v1130 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1130 s i = 1 := by
  change (if (1073741875 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 4261441663 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_sub_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sub_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073741875 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_sub_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1046 s i commit known, ref_sub_v1052 s i commit known, ref_sub_v1058 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v1131, v1132, ref_sub_v1333 s i commit known, ref_sub_v1339 s i commit known, ref_sub_v1345 s i commit known, ref_sub_v1351 s i commit known, ref_sub_v1358 s i commit known, ref_sub_v1365 s i commit known, ref_sub_v1372 s i commit known, ref_sub_v1379 s i commit known, ref_sub_v1386 s i commit known, v1577, v1612, v1613, v1614, v1615, v1616, v1617, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_sub_rs2 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) :
    v1427 s i = BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v1131, ref_sub_v1333 s i commit known, ref_sub_v1339 s i commit known, ref_sub_v1345 s i commit known, ref_sub_v1351 s i commit known, ref_sub_v1358 s i commit known, ref_sub_v1365 s i commit known, ref_sub_v1372 s i commit known, ref_sub_v1379 s i commit known, ref_sub_v1386 s i commit known, v1391, v1408, v1409, v1410, v1411, v1412, v1413, v1414, v1415, v1416, v1417, v1418, v1419, v1420, v1421, v1422, v1423, v1424, v1425, v1426, v1427, commit, reference_commit_instruction s i commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 20+j < 25 by omega, show 20+j < 31 by omega, show 20+j < 32 by omega]
theorem reference_sub_rd (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) :
    v1320 s i = BitVec.extractLsb' 7 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1046 s i commit known, ref_sub_v1052 s i commit known, ref_sub_v1058 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v1131, v1132, v1133, v1134, v1135, v1300, v1301, v1302, v1303, v1304, v1305, v1306, v1307, v1308, v1309, v1310, v1311, v1312, v1313, v1314, v1315, v1316, v1317, v1318, v1319, v1320, commit, reference_commit_instruction s i commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega, show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 25 by omega, show 7+j < 31 by omega, show 7+j < 32 by omega]
theorem reference_sub_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_sub_rs1 s i commit known]
theorem reference_sub_operand2 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) :
    v1539 s i = referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port2 s i zero, reference_sub_rs2 s i commit known]
theorem aligned_reference_arithmetic_sub (s : State) (i : Inputs)
    (aligned : DecodedAluAligned s) (agree : RegisterAgreement s)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2266 s i := by
  have arithmetic := decoded_reference_arithmetic_sub s i s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
    s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc known
  rw [reference_sub_operand1 s i zero commit known,
    reference_sub_operand2 s i zero commit known] at arithmetic
  exact (decoded_alu_reference_operands s aligned agree).trans arithmetic
#print axioms aligned_reference_arithmetic_sub
private theorem reference_sub_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2266 s i := by
  change (v2431 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v2261, v2262, v2390, v2391, v2393, v2396, v2399, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2266 s i := by
  change (v2585 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v2466, v2467, v2544, v2545, v2547, v2550, v2553, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2266 s i := by
  change (v2739 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v2620, v2621, v2698, v2699, v2701, v2704, v2707, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2266 s i := by
  change (v2893 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v2774, v2775, v2852, v2853, v2855, v2858, v2861, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2266 s i := by
  change (v3047 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v2928, v2929, v3006, v3007, v3009, v3012, v3015, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2266 s i := by
  change (v3201 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v3082, v3083, v3160, v3161, v3163, v3166, v3169, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2266 s i := by
  change (v3355 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v3236, v3237, v3314, v3315, v3317, v3320, v3323, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2266 s i := by
  change (v3509 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v3390, v3391, v3468, v3469, v3471, v3474, v3477, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2266 s i := by
  change (v3663 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v3544, v3545, v3622, v3623, v3625, v3628, v3631, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2266 s i := by
  change (v3817 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v3698, v3699, v3776, v3777, v3779, v3782, v3785, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2266 s i := by
  change (v3971 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v3852, v3853, v3930, v3931, v3933, v3936, v3939, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2266 s i := by
  change (v4125 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v4006, v4007, v4084, v4085, v4087, v4090, v4093, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2266 s i := by
  change (v4279 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v4160, v4161, v4238, v4239, v4241, v4244, v4247, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2266 s i := by
  change (v4433 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v4314, v4315, v4392, v4393, v4395, v4398, v4401, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2266 s i := by
  change (v4587 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v4468, v4469, v4546, v4547, v4549, v4552, v4555, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2266 s i := by
  change (v4705 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v4606, v4664, v4665, v4667, v4670, v4673, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2266 s i := by
  change (v4823 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v4724, v4782, v4783, v4785, v4788, v4791, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2266 s i := by
  change (v4941 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v4842, v4900, v4901, v4903, v4906, v4909, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2266 s i := by
  change (v5059 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v4960, v5018, v5019, v5021, v5024, v5027, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2266 s i := by
  change (v5177 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v5078, v5136, v5137, v5139, v5142, v5145, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2266 s i := by
  change (v5295 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v5196, v5254, v5255, v5257, v5260, v5263, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2266 s i := by
  change (v5413 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v5314, v5372, v5373, v5375, v5378, v5381, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2266 s i := by
  change (v5531 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v5432, v5490, v5491, v5493, v5496, v5499, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2266 s i := by
  change (v5649 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v5550, v5608, v5609, v5611, v5614, v5617, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2266 s i := by
  change (v5767 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v5668, v5726, v5727, v5729, v5732, v5735, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2266 s i := by
  change (v5885 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v5786, v5844, v5845, v5847, v5850, v5853, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2266 s i := by
  change (v6003 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v5904, v5962, v5963, v5965, v5968, v5971, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2266 s i := by
  change (v6121 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v6022, v6080, v6081, v6083, v6086, v6089, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2266 s i := by
  change (v6239 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v6140, v6198, v6199, v6201, v6204, v6207, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2266 s i := by
  change (v6357 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v6258, v6316, v6317, v6319, v6322, v6325, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
private theorem reference_sub_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2266 s i := by
  change (v6475 s i) = v2266 s i
  simp [v0, v1, ref_sub_v1005 s i commit known, ref_sub_v1013 s i commit known, ref_sub_v1021 s i commit known, ref_sub_v1029 s i commit known, ref_sub_v1037 s i commit known, ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, ref_sub_v1106 s i commit known, ref_sub_v1114 s i commit known, ref_sub_v1122 s i commit known, ref_sub_v1130 s i commit known, v6376, v6434, v6435, v6437, v6440, v6443, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_sub_v980 s i commit known, ref_sub_v989 s i commit known, ref_sub_v997 s i commit known, reset, target]
theorem reference_sub_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2266 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x1 s i reset commit known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x2 s i reset commit known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x3 s i reset commit known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x4 s i reset commit known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x5 s i reset commit known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x6 s i reset commit known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x7 s i reset commit known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x8 s i reset commit known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x9 s i reset commit known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x10 s i reset commit known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x11 s i reset commit known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x12 s i reset commit known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x13 s i reset commit known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x14 s i reset commit known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x15 s i reset commit known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x16 s i reset commit known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x17 s i reset commit known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x18 s i reset commit known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x19 s i reset commit known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x20 s i reset commit known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x21 s i reset commit known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x22 s i reset commit known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x23 s i reset commit known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x24 s i reset commit known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x25 s i reset commit known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x26 s i reset commit known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x27 s i reset commit known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x28 s i reset commit known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x29 s i reset commit known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x30 s i reset commit known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_sub_rd s i commit known).trans target
    rw [target]
    exact reference_sub_next_x31 s i reset commit known refTarget
#print axioms reference_sub_written_value
private theorem ref_sll_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_sll_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_sll_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1122 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1122 s i = 0 := by
  change (if (1073762355 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1130 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1130 s i = 0 := by
  change (if (1073741875 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1138 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1138 s i = 0 := by
  change (if (20531 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1146 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1146 s i = 1 := by
  change (if (4147 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 4261441663 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_sll_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sll_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4147 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_sll_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1046 s i commit known, ref_sll_v1052 s i commit known, ref_sll_v1058 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v1147, v1148, ref_sll_v1333 s i commit known, ref_sll_v1339 s i commit known, ref_sll_v1345 s i commit known, ref_sll_v1351 s i commit known, ref_sll_v1358 s i commit known, ref_sll_v1365 s i commit known, ref_sll_v1372 s i commit known, ref_sll_v1379 s i commit known, ref_sll_v1386 s i commit known, v1579, v1610, v1611, v1612, v1613, v1614, v1615, v1616, v1617, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_sll_rs2 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) :
    v1427 s i = BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v1147, ref_sll_v1333 s i commit known, ref_sll_v1339 s i commit known, ref_sll_v1345 s i commit known, ref_sll_v1351 s i commit known, ref_sll_v1358 s i commit known, ref_sll_v1365 s i commit known, ref_sll_v1372 s i commit known, ref_sll_v1379 s i commit known, ref_sll_v1386 s i commit known, v1393, v1406, v1407, v1408, v1409, v1410, v1411, v1412, v1413, v1414, v1415, v1416, v1417, v1418, v1419, v1420, v1421, v1422, v1423, v1424, v1425, v1426, v1427, commit, reference_commit_instruction s i commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 20+j < 25 by omega, show 20+j < 31 by omega, show 20+j < 32 by omega]
theorem reference_sll_rd (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) :
    v1320 s i = BitVec.extractLsb' 7 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1046 s i commit known, ref_sll_v1052 s i commit known, ref_sll_v1058 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v1147, v1148, v1149, v1150, v1151, v1298, v1299, v1300, v1301, v1302, v1303, v1304, v1305, v1306, v1307, v1308, v1309, v1310, v1311, v1312, v1313, v1314, v1315, v1316, v1317, v1318, v1319, v1320, commit, reference_commit_instruction s i commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega, show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 25 by omega, show 7+j < 31 by omega, show 7+j < 32 by omega]
theorem reference_sll_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_sll_rs1 s i commit known]
theorem reference_sll_operand2 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) :
    v1539 s i = referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port2 s i zero, reference_sll_rs2 s i commit known]
theorem aligned_reference_arithmetic_sll (s : State) (i : Inputs)
    (aligned : DecodedAluAligned s) (agree : RegisterAgreement s)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2280 s i := by
  have arithmetic := decoded_reference_arithmetic_sll s i s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
    s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc known
  rw [reference_sll_operand1 s i zero commit known,
    reference_sll_operand2 s i zero commit known] at arithmetic
  exact (decoded_alu_reference_operands s aligned agree).trans arithmetic
#print axioms aligned_reference_arithmetic_sll
private theorem reference_sll_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2280 s i := by
  change (v2431 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v2272, v2273, v2386, v2387, v2389, v2391, v2393, v2396, v2399, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2280 s i := by
  change (v2585 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v2470, v2471, v2540, v2541, v2543, v2545, v2547, v2550, v2553, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2280 s i := by
  change (v2739 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v2624, v2625, v2694, v2695, v2697, v2699, v2701, v2704, v2707, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2280 s i := by
  change (v2893 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v2778, v2779, v2848, v2849, v2851, v2853, v2855, v2858, v2861, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2280 s i := by
  change (v3047 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v2932, v2933, v3002, v3003, v3005, v3007, v3009, v3012, v3015, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2280 s i := by
  change (v3201 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v3086, v3087, v3156, v3157, v3159, v3161, v3163, v3166, v3169, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2280 s i := by
  change (v3355 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v3240, v3241, v3310, v3311, v3313, v3315, v3317, v3320, v3323, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2280 s i := by
  change (v3509 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v3394, v3395, v3464, v3465, v3467, v3469, v3471, v3474, v3477, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2280 s i := by
  change (v3663 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v3548, v3549, v3618, v3619, v3621, v3623, v3625, v3628, v3631, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2280 s i := by
  change (v3817 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v3702, v3703, v3772, v3773, v3775, v3777, v3779, v3782, v3785, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2280 s i := by
  change (v3971 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v3856, v3857, v3926, v3927, v3929, v3931, v3933, v3936, v3939, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2280 s i := by
  change (v4125 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v4010, v4011, v4080, v4081, v4083, v4085, v4087, v4090, v4093, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2280 s i := by
  change (v4279 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v4164, v4165, v4234, v4235, v4237, v4239, v4241, v4244, v4247, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2280 s i := by
  change (v4433 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v4318, v4319, v4388, v4389, v4391, v4393, v4395, v4398, v4401, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2280 s i := by
  change (v4587 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v4472, v4473, v4542, v4543, v4545, v4547, v4549, v4552, v4555, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2280 s i := by
  change (v4705 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v4608, v4660, v4661, v4663, v4665, v4667, v4670, v4673, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2280 s i := by
  change (v4823 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v4726, v4778, v4779, v4781, v4783, v4785, v4788, v4791, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2280 s i := by
  change (v4941 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v4844, v4896, v4897, v4899, v4901, v4903, v4906, v4909, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2280 s i := by
  change (v5059 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v4962, v5014, v5015, v5017, v5019, v5021, v5024, v5027, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2280 s i := by
  change (v5177 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v5080, v5132, v5133, v5135, v5137, v5139, v5142, v5145, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2280 s i := by
  change (v5295 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v5198, v5250, v5251, v5253, v5255, v5257, v5260, v5263, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2280 s i := by
  change (v5413 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v5316, v5368, v5369, v5371, v5373, v5375, v5378, v5381, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2280 s i := by
  change (v5531 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v5434, v5486, v5487, v5489, v5491, v5493, v5496, v5499, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2280 s i := by
  change (v5649 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v5552, v5604, v5605, v5607, v5609, v5611, v5614, v5617, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2280 s i := by
  change (v5767 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v5670, v5722, v5723, v5725, v5727, v5729, v5732, v5735, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2280 s i := by
  change (v5885 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v5788, v5840, v5841, v5843, v5845, v5847, v5850, v5853, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2280 s i := by
  change (v6003 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v5906, v5958, v5959, v5961, v5963, v5965, v5968, v5971, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2280 s i := by
  change (v6121 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v6024, v6076, v6077, v6079, v6081, v6083, v6086, v6089, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2280 s i := by
  change (v6239 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v6142, v6194, v6195, v6197, v6199, v6201, v6204, v6207, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2280 s i := by
  change (v6357 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v6260, v6312, v6313, v6315, v6317, v6319, v6322, v6325, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
private theorem reference_sll_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2280 s i := by
  change (v6475 s i) = v2280 s i
  simp [v0, v1, ref_sll_v1005 s i commit known, ref_sll_v1013 s i commit known, ref_sll_v1021 s i commit known, ref_sll_v1029 s i commit known, ref_sll_v1037 s i commit known, ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, ref_sll_v1106 s i commit known, ref_sll_v1114 s i commit known, ref_sll_v1122 s i commit known, ref_sll_v1130 s i commit known, ref_sll_v1138 s i commit known, ref_sll_v1146 s i commit known, v6378, v6430, v6431, v6433, v6435, v6437, v6440, v6443, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_sll_v980 s i commit known, ref_sll_v989 s i commit known, ref_sll_v997 s i commit known, reset, target]
theorem reference_sll_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2280 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x1 s i reset commit known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x2 s i reset commit known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x3 s i reset commit known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x4 s i reset commit known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x5 s i reset commit known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x6 s i reset commit known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x7 s i reset commit known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x8 s i reset commit known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x9 s i reset commit known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x10 s i reset commit known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x11 s i reset commit known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x12 s i reset commit known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x13 s i reset commit known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x14 s i reset commit known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x15 s i reset commit known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x16 s i reset commit known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x17 s i reset commit known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x18 s i reset commit known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x19 s i reset commit known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x20 s i reset commit known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x21 s i reset commit known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x22 s i reset commit known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x23 s i reset commit known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x24 s i reset commit known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x25 s i reset commit known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x26 s i reset commit known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x27 s i reset commit known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x28 s i reset commit known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x29 s i reset commit known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x30 s i reset commit known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_sll_rd s i commit known).trans target
    rw [target]
    exact reference_sll_next_x31 s i reset commit known refTarget
#print axioms reference_sll_written_value
private theorem ref_slt_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_slt_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_slt_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1122 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1122 s i = 0 := by
  change (if (1073762355 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1130 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1130 s i = 0 := by
  change (if (1073741875 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1138 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1138 s i = 0 := by
  change (if (20531 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1146 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1146 s i = 0 := by
  change (if (4147 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1154 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1154 s i = 0 := by
  change (if (16435 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1162 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1162 s i = 0 := by
  change (if (24627 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 4261441663 24627 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1170 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1170 s i = 0 := by
  change (if (28723 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 4261441663 28723 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1178 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1178 s i = 0 := by
  change (if (12339 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1186 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1186 s i = 1 := by
  change (if (8243 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 4261441663 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_slt_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slt_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 8243 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_slt_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1046 s i commit known, ref_slt_v1052 s i commit known, ref_slt_v1058 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v1187, v1188, ref_slt_v1333 s i commit known, ref_slt_v1339 s i commit known, ref_slt_v1345 s i commit known, ref_slt_v1351 s i commit known, ref_slt_v1358 s i commit known, ref_slt_v1365 s i commit known, ref_slt_v1372 s i commit known, ref_slt_v1379 s i commit known, ref_slt_v1386 s i commit known, v1584, v1605, v1606, v1607, v1608, v1609, v1610, v1611, v1612, v1613, v1614, v1615, v1616, v1617, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_slt_rs2 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) :
    v1427 s i = BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v1187, ref_slt_v1333 s i commit known, ref_slt_v1339 s i commit known, ref_slt_v1345 s i commit known, ref_slt_v1351 s i commit known, ref_slt_v1358 s i commit known, ref_slt_v1365 s i commit known, ref_slt_v1372 s i commit known, ref_slt_v1379 s i commit known, ref_slt_v1386 s i commit known, v1398, v1401, v1402, v1403, v1404, v1405, v1406, v1407, v1408, v1409, v1410, v1411, v1412, v1413, v1414, v1415, v1416, v1417, v1418, v1419, v1420, v1421, v1422, v1423, v1424, v1425, v1426, v1427, commit, reference_commit_instruction s i commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 20+j < 25 by omega, show 20+j < 31 by omega, show 20+j < 32 by omega]
theorem reference_slt_rd (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) :
    v1320 s i = BitVec.extractLsb' 7 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1046 s i commit known, ref_slt_v1052 s i commit known, ref_slt_v1058 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v1187, v1188, v1189, v1190, v1191, v1293, v1294, v1295, v1296, v1297, v1298, v1299, v1300, v1301, v1302, v1303, v1304, v1305, v1306, v1307, v1308, v1309, v1310, v1311, v1312, v1313, v1314, v1315, v1316, v1317, v1318, v1319, v1320, commit, reference_commit_instruction s i commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega, show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 25 by omega, show 7+j < 31 by omega, show 7+j < 32 by omega]
theorem reference_slt_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_slt_rs1 s i commit known]
theorem reference_slt_operand2 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) :
    v1539 s i = referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port2 s i zero, reference_slt_rs2 s i commit known]
theorem aligned_reference_arithmetic_slt (s : State) (i : Inputs)
    (aligned : DecodedAluAligned s) (agree : RegisterAgreement s)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2297 s i := by
  have arithmetic := decoded_reference_arithmetic_slt s i s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
    s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc known
  rw [reference_slt_operand1 s i zero commit known,
    reference_slt_operand2 s i zero commit known] at arithmetic
  exact (decoded_alu_reference_operands s aligned agree).trans arithmetic
#print axioms aligned_reference_arithmetic_slt
private theorem reference_slt_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2297 s i := by
  change (v2431 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v2294, v2295, v2376, v2377, v2379, v2381, v2383, v2385, v2387, v2389, v2391, v2393, v2396, v2399, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2297 s i := by
  change (v2585 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v2480, v2481, v2530, v2531, v2533, v2535, v2537, v2539, v2541, v2543, v2545, v2547, v2550, v2553, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2297 s i := by
  change (v2739 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v2634, v2635, v2684, v2685, v2687, v2689, v2691, v2693, v2695, v2697, v2699, v2701, v2704, v2707, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2297 s i := by
  change (v2893 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v2788, v2789, v2838, v2839, v2841, v2843, v2845, v2847, v2849, v2851, v2853, v2855, v2858, v2861, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2297 s i := by
  change (v3047 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v2942, v2943, v2992, v2993, v2995, v2997, v2999, v3001, v3003, v3005, v3007, v3009, v3012, v3015, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2297 s i := by
  change (v3201 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v3096, v3097, v3146, v3147, v3149, v3151, v3153, v3155, v3157, v3159, v3161, v3163, v3166, v3169, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2297 s i := by
  change (v3355 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v3250, v3251, v3300, v3301, v3303, v3305, v3307, v3309, v3311, v3313, v3315, v3317, v3320, v3323, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2297 s i := by
  change (v3509 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v3404, v3405, v3454, v3455, v3457, v3459, v3461, v3463, v3465, v3467, v3469, v3471, v3474, v3477, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2297 s i := by
  change (v3663 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v3558, v3559, v3608, v3609, v3611, v3613, v3615, v3617, v3619, v3621, v3623, v3625, v3628, v3631, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2297 s i := by
  change (v3817 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v3712, v3713, v3762, v3763, v3765, v3767, v3769, v3771, v3773, v3775, v3777, v3779, v3782, v3785, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2297 s i := by
  change (v3971 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v3866, v3867, v3916, v3917, v3919, v3921, v3923, v3925, v3927, v3929, v3931, v3933, v3936, v3939, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2297 s i := by
  change (v4125 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v4020, v4021, v4070, v4071, v4073, v4075, v4077, v4079, v4081, v4083, v4085, v4087, v4090, v4093, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2297 s i := by
  change (v4279 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v4174, v4175, v4224, v4225, v4227, v4229, v4231, v4233, v4235, v4237, v4239, v4241, v4244, v4247, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2297 s i := by
  change (v4433 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v4328, v4329, v4378, v4379, v4381, v4383, v4385, v4387, v4389, v4391, v4393, v4395, v4398, v4401, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2297 s i := by
  change (v4587 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v4482, v4483, v4532, v4533, v4535, v4537, v4539, v4541, v4543, v4545, v4547, v4549, v4552, v4555, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2297 s i := by
  change (v4705 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v4613, v4650, v4651, v4653, v4655, v4657, v4659, v4661, v4663, v4665, v4667, v4670, v4673, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2297 s i := by
  change (v4823 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v4731, v4768, v4769, v4771, v4773, v4775, v4777, v4779, v4781, v4783, v4785, v4788, v4791, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2297 s i := by
  change (v4941 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v4849, v4886, v4887, v4889, v4891, v4893, v4895, v4897, v4899, v4901, v4903, v4906, v4909, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2297 s i := by
  change (v5059 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v4967, v5004, v5005, v5007, v5009, v5011, v5013, v5015, v5017, v5019, v5021, v5024, v5027, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2297 s i := by
  change (v5177 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v5085, v5122, v5123, v5125, v5127, v5129, v5131, v5133, v5135, v5137, v5139, v5142, v5145, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2297 s i := by
  change (v5295 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v5203, v5240, v5241, v5243, v5245, v5247, v5249, v5251, v5253, v5255, v5257, v5260, v5263, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2297 s i := by
  change (v5413 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v5321, v5358, v5359, v5361, v5363, v5365, v5367, v5369, v5371, v5373, v5375, v5378, v5381, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2297 s i := by
  change (v5531 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v5439, v5476, v5477, v5479, v5481, v5483, v5485, v5487, v5489, v5491, v5493, v5496, v5499, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2297 s i := by
  change (v5649 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v5557, v5594, v5595, v5597, v5599, v5601, v5603, v5605, v5607, v5609, v5611, v5614, v5617, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2297 s i := by
  change (v5767 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v5675, v5712, v5713, v5715, v5717, v5719, v5721, v5723, v5725, v5727, v5729, v5732, v5735, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2297 s i := by
  change (v5885 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v5793, v5830, v5831, v5833, v5835, v5837, v5839, v5841, v5843, v5845, v5847, v5850, v5853, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2297 s i := by
  change (v6003 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v5911, v5948, v5949, v5951, v5953, v5955, v5957, v5959, v5961, v5963, v5965, v5968, v5971, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2297 s i := by
  change (v6121 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v6029, v6066, v6067, v6069, v6071, v6073, v6075, v6077, v6079, v6081, v6083, v6086, v6089, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2297 s i := by
  change (v6239 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v6147, v6184, v6185, v6187, v6189, v6191, v6193, v6195, v6197, v6199, v6201, v6204, v6207, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2297 s i := by
  change (v6357 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v6265, v6302, v6303, v6305, v6307, v6309, v6311, v6313, v6315, v6317, v6319, v6322, v6325, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
private theorem reference_slt_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2297 s i := by
  change (v6475 s i) = v2297 s i
  simp [v0, v1, ref_slt_v1005 s i commit known, ref_slt_v1013 s i commit known, ref_slt_v1021 s i commit known, ref_slt_v1029 s i commit known, ref_slt_v1037 s i commit known, ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, ref_slt_v1106 s i commit known, ref_slt_v1114 s i commit known, ref_slt_v1122 s i commit known, ref_slt_v1130 s i commit known, ref_slt_v1138 s i commit known, ref_slt_v1146 s i commit known, ref_slt_v1154 s i commit known, ref_slt_v1162 s i commit known, ref_slt_v1170 s i commit known, ref_slt_v1178 s i commit known, ref_slt_v1186 s i commit known, v6383, v6420, v6421, v6423, v6425, v6427, v6429, v6431, v6433, v6435, v6437, v6440, v6443, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_slt_v980 s i commit known, ref_slt_v989 s i commit known, ref_slt_v997 s i commit known, reset, target]
theorem reference_slt_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2297 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x1 s i reset commit known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x2 s i reset commit known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x3 s i reset commit known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x4 s i reset commit known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x5 s i reset commit known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x6 s i reset commit known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x7 s i reset commit known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x8 s i reset commit known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x9 s i reset commit known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x10 s i reset commit known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x11 s i reset commit known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x12 s i reset commit known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x13 s i reset commit known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x14 s i reset commit known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x15 s i reset commit known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x16 s i reset commit known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x17 s i reset commit known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x18 s i reset commit known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x19 s i reset commit known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x20 s i reset commit known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x21 s i reset commit known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x22 s i reset commit known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x23 s i reset commit known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x24 s i reset commit known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x25 s i reset commit known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x26 s i reset commit known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x27 s i reset commit known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x28 s i reset commit known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x29 s i reset commit known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x30 s i reset commit known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_slt_rd s i commit known).trans target
    rw [target]
    exact reference_slt_next_x31 s i reset commit known refTarget
#print axioms reference_slt_written_value
private theorem ref_sltu_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_sltu_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_sltu_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1122 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1122 s i = 0 := by
  change (if (1073762355 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1130 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1130 s i = 0 := by
  change (if (1073741875 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1138 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1138 s i = 0 := by
  change (if (20531 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1146 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1146 s i = 0 := by
  change (if (4147 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1154 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1154 s i = 0 := by
  change (if (16435 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1162 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1162 s i = 0 := by
  change (if (24627 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 4261441663 24627 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1170 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1170 s i = 0 := by
  change (if (28723 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 4261441663 28723 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1178 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1178 s i = 1 := by
  change (if (12339 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 4261441663 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_sltu_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltu_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 12339 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_sltu_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1046 s i commit known, ref_sltu_v1052 s i commit known, ref_sltu_v1058 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v1179, v1180, ref_sltu_v1333 s i commit known, ref_sltu_v1339 s i commit known, ref_sltu_v1345 s i commit known, ref_sltu_v1351 s i commit known, ref_sltu_v1358 s i commit known, ref_sltu_v1365 s i commit known, ref_sltu_v1372 s i commit known, ref_sltu_v1379 s i commit known, ref_sltu_v1386 s i commit known, v1583, v1606, v1607, v1608, v1609, v1610, v1611, v1612, v1613, v1614, v1615, v1616, v1617, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_sltu_rs2 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) :
    v1427 s i = BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v1179, ref_sltu_v1333 s i commit known, ref_sltu_v1339 s i commit known, ref_sltu_v1345 s i commit known, ref_sltu_v1351 s i commit known, ref_sltu_v1358 s i commit known, ref_sltu_v1365 s i commit known, ref_sltu_v1372 s i commit known, ref_sltu_v1379 s i commit known, ref_sltu_v1386 s i commit known, v1397, v1402, v1403, v1404, v1405, v1406, v1407, v1408, v1409, v1410, v1411, v1412, v1413, v1414, v1415, v1416, v1417, v1418, v1419, v1420, v1421, v1422, v1423, v1424, v1425, v1426, v1427, commit, reference_commit_instruction s i commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 20+j < 25 by omega, show 20+j < 31 by omega, show 20+j < 32 by omega]
theorem reference_sltu_rd (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) :
    v1320 s i = BitVec.extractLsb' 7 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1046 s i commit known, ref_sltu_v1052 s i commit known, ref_sltu_v1058 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v1179, v1180, v1181, v1182, v1183, v1294, v1295, v1296, v1297, v1298, v1299, v1300, v1301, v1302, v1303, v1304, v1305, v1306, v1307, v1308, v1309, v1310, v1311, v1312, v1313, v1314, v1315, v1316, v1317, v1318, v1319, v1320, commit, reference_commit_instruction s i commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega, show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 25 by omega, show 7+j < 31 by omega, show 7+j < 32 by omega]
theorem reference_sltu_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_sltu_rs1 s i commit known]
theorem reference_sltu_operand2 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) :
    v1539 s i = referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port2 s i zero, reference_sltu_rs2 s i commit known]
theorem aligned_reference_arithmetic_sltu (s : State) (i : Inputs)
    (aligned : DecodedAluAligned s) (agree : RegisterAgreement s)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2293 s i := by
  have arithmetic := decoded_reference_arithmetic_sltu s i s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
    s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc known
  rw [reference_sltu_operand1 s i zero commit known,
    reference_sltu_operand2 s i zero commit known] at arithmetic
  exact (decoded_alu_reference_operands s aligned agree).trans arithmetic
#print axioms aligned_reference_arithmetic_sltu
private theorem reference_sltu_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2293 s i := by
  change (v2431 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v2290, v2291, v2378, v2379, v2381, v2383, v2385, v2387, v2389, v2391, v2393, v2396, v2399, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2293 s i := by
  change (v2585 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v2478, v2479, v2532, v2533, v2535, v2537, v2539, v2541, v2543, v2545, v2547, v2550, v2553, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2293 s i := by
  change (v2739 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v2632, v2633, v2686, v2687, v2689, v2691, v2693, v2695, v2697, v2699, v2701, v2704, v2707, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2293 s i := by
  change (v2893 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v2786, v2787, v2840, v2841, v2843, v2845, v2847, v2849, v2851, v2853, v2855, v2858, v2861, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2293 s i := by
  change (v3047 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v2940, v2941, v2994, v2995, v2997, v2999, v3001, v3003, v3005, v3007, v3009, v3012, v3015, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2293 s i := by
  change (v3201 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v3094, v3095, v3148, v3149, v3151, v3153, v3155, v3157, v3159, v3161, v3163, v3166, v3169, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2293 s i := by
  change (v3355 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v3248, v3249, v3302, v3303, v3305, v3307, v3309, v3311, v3313, v3315, v3317, v3320, v3323, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2293 s i := by
  change (v3509 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v3402, v3403, v3456, v3457, v3459, v3461, v3463, v3465, v3467, v3469, v3471, v3474, v3477, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2293 s i := by
  change (v3663 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v3556, v3557, v3610, v3611, v3613, v3615, v3617, v3619, v3621, v3623, v3625, v3628, v3631, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2293 s i := by
  change (v3817 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v3710, v3711, v3764, v3765, v3767, v3769, v3771, v3773, v3775, v3777, v3779, v3782, v3785, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2293 s i := by
  change (v3971 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v3864, v3865, v3918, v3919, v3921, v3923, v3925, v3927, v3929, v3931, v3933, v3936, v3939, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2293 s i := by
  change (v4125 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v4018, v4019, v4072, v4073, v4075, v4077, v4079, v4081, v4083, v4085, v4087, v4090, v4093, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2293 s i := by
  change (v4279 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v4172, v4173, v4226, v4227, v4229, v4231, v4233, v4235, v4237, v4239, v4241, v4244, v4247, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2293 s i := by
  change (v4433 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v4326, v4327, v4380, v4381, v4383, v4385, v4387, v4389, v4391, v4393, v4395, v4398, v4401, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2293 s i := by
  change (v4587 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v4480, v4481, v4534, v4535, v4537, v4539, v4541, v4543, v4545, v4547, v4549, v4552, v4555, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2293 s i := by
  change (v4705 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v4612, v4652, v4653, v4655, v4657, v4659, v4661, v4663, v4665, v4667, v4670, v4673, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2293 s i := by
  change (v4823 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v4730, v4770, v4771, v4773, v4775, v4777, v4779, v4781, v4783, v4785, v4788, v4791, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2293 s i := by
  change (v4941 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v4848, v4888, v4889, v4891, v4893, v4895, v4897, v4899, v4901, v4903, v4906, v4909, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2293 s i := by
  change (v5059 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v4966, v5006, v5007, v5009, v5011, v5013, v5015, v5017, v5019, v5021, v5024, v5027, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2293 s i := by
  change (v5177 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v5084, v5124, v5125, v5127, v5129, v5131, v5133, v5135, v5137, v5139, v5142, v5145, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2293 s i := by
  change (v5295 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v5202, v5242, v5243, v5245, v5247, v5249, v5251, v5253, v5255, v5257, v5260, v5263, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2293 s i := by
  change (v5413 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v5320, v5360, v5361, v5363, v5365, v5367, v5369, v5371, v5373, v5375, v5378, v5381, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2293 s i := by
  change (v5531 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v5438, v5478, v5479, v5481, v5483, v5485, v5487, v5489, v5491, v5493, v5496, v5499, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2293 s i := by
  change (v5649 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v5556, v5596, v5597, v5599, v5601, v5603, v5605, v5607, v5609, v5611, v5614, v5617, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2293 s i := by
  change (v5767 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v5674, v5714, v5715, v5717, v5719, v5721, v5723, v5725, v5727, v5729, v5732, v5735, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2293 s i := by
  change (v5885 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v5792, v5832, v5833, v5835, v5837, v5839, v5841, v5843, v5845, v5847, v5850, v5853, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2293 s i := by
  change (v6003 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v5910, v5950, v5951, v5953, v5955, v5957, v5959, v5961, v5963, v5965, v5968, v5971, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2293 s i := by
  change (v6121 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v6028, v6068, v6069, v6071, v6073, v6075, v6077, v6079, v6081, v6083, v6086, v6089, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2293 s i := by
  change (v6239 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v6146, v6186, v6187, v6189, v6191, v6193, v6195, v6197, v6199, v6201, v6204, v6207, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2293 s i := by
  change (v6357 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v6264, v6304, v6305, v6307, v6309, v6311, v6313, v6315, v6317, v6319, v6322, v6325, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
private theorem reference_sltu_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2293 s i := by
  change (v6475 s i) = v2293 s i
  simp [v0, v1, ref_sltu_v1005 s i commit known, ref_sltu_v1013 s i commit known, ref_sltu_v1021 s i commit known, ref_sltu_v1029 s i commit known, ref_sltu_v1037 s i commit known, ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, ref_sltu_v1106 s i commit known, ref_sltu_v1114 s i commit known, ref_sltu_v1122 s i commit known, ref_sltu_v1130 s i commit known, ref_sltu_v1138 s i commit known, ref_sltu_v1146 s i commit known, ref_sltu_v1154 s i commit known, ref_sltu_v1162 s i commit known, ref_sltu_v1170 s i commit known, ref_sltu_v1178 s i commit known, v6382, v6422, v6423, v6425, v6427, v6429, v6431, v6433, v6435, v6437, v6440, v6443, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_sltu_v980 s i commit known, ref_sltu_v989 s i commit known, ref_sltu_v997 s i commit known, reset, target]
theorem reference_sltu_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2293 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x1 s i reset commit known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x2 s i reset commit known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x3 s i reset commit known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x4 s i reset commit known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x5 s i reset commit known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x6 s i reset commit known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x7 s i reset commit known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x8 s i reset commit known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x9 s i reset commit known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x10 s i reset commit known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x11 s i reset commit known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x12 s i reset commit known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x13 s i reset commit known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x14 s i reset commit known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x15 s i reset commit known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x16 s i reset commit known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x17 s i reset commit known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x18 s i reset commit known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x19 s i reset commit known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x20 s i reset commit known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x21 s i reset commit known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x22 s i reset commit known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x23 s i reset commit known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x24 s i reset commit known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x25 s i reset commit known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x26 s i reset commit known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x27 s i reset commit known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x28 s i reset commit known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x29 s i reset commit known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x30 s i reset commit known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_sltu_rd s i commit known).trans target
    rw [target]
    exact reference_sltu_next_x31 s i reset commit known refTarget
#print axioms reference_sltu_written_value
private theorem ref_xor_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_xor_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_xor_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1122 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1122 s i = 0 := by
  change (if (1073762355 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1130 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1130 s i = 0 := by
  change (if (1073741875 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1138 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1138 s i = 0 := by
  change (if (20531 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1146 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1146 s i = 0 := by
  change (if (4147 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1154 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1154 s i = 1 := by
  change (if (16435 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 4261441663 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_xor_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xor_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 16435 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_xor_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1046 s i commit known, ref_xor_v1052 s i commit known, ref_xor_v1058 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v1155, v1156, ref_xor_v1333 s i commit known, ref_xor_v1339 s i commit known, ref_xor_v1345 s i commit known, ref_xor_v1351 s i commit known, ref_xor_v1358 s i commit known, ref_xor_v1365 s i commit known, ref_xor_v1372 s i commit known, ref_xor_v1379 s i commit known, ref_xor_v1386 s i commit known, v1580, v1609, v1610, v1611, v1612, v1613, v1614, v1615, v1616, v1617, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_xor_rs2 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) :
    v1427 s i = BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v1155, ref_xor_v1333 s i commit known, ref_xor_v1339 s i commit known, ref_xor_v1345 s i commit known, ref_xor_v1351 s i commit known, ref_xor_v1358 s i commit known, ref_xor_v1365 s i commit known, ref_xor_v1372 s i commit known, ref_xor_v1379 s i commit known, ref_xor_v1386 s i commit known, v1394, v1405, v1406, v1407, v1408, v1409, v1410, v1411, v1412, v1413, v1414, v1415, v1416, v1417, v1418, v1419, v1420, v1421, v1422, v1423, v1424, v1425, v1426, v1427, commit, reference_commit_instruction s i commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 20+j < 25 by omega, show 20+j < 31 by omega, show 20+j < 32 by omega]
theorem reference_xor_rd (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) :
    v1320 s i = BitVec.extractLsb' 7 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1046 s i commit known, ref_xor_v1052 s i commit known, ref_xor_v1058 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v1155, v1156, v1157, v1158, v1159, v1297, v1298, v1299, v1300, v1301, v1302, v1303, v1304, v1305, v1306, v1307, v1308, v1309, v1310, v1311, v1312, v1313, v1314, v1315, v1316, v1317, v1318, v1319, v1320, commit, reference_commit_instruction s i commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega, show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 25 by omega, show 7+j < 31 by omega, show 7+j < 32 by omega]
theorem reference_xor_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_xor_rs1 s i commit known]
theorem reference_xor_operand2 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) :
    v1539 s i = referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port2 s i zero, reference_xor_rs2 s i commit known]
theorem aligned_reference_arithmetic_xor (s : State) (i : Inputs)
    (aligned : DecodedAluAligned s) (agree : RegisterAgreement s)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2283 s i := by
  have arithmetic := decoded_reference_arithmetic_xor s i s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
    s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc known
  rw [reference_xor_operand1 s i zero commit known,
    reference_xor_operand2 s i zero commit known] at arithmetic
  exact (decoded_alu_reference_operands s aligned agree).trans arithmetic
#print axioms aligned_reference_arithmetic_xor
private theorem reference_xor_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2283 s i := by
  change (v2431 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v2281, v2282, v2384, v2385, v2387, v2389, v2391, v2393, v2396, v2399, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2283 s i := by
  change (v2585 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v2472, v2473, v2538, v2539, v2541, v2543, v2545, v2547, v2550, v2553, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2283 s i := by
  change (v2739 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v2626, v2627, v2692, v2693, v2695, v2697, v2699, v2701, v2704, v2707, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2283 s i := by
  change (v2893 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v2780, v2781, v2846, v2847, v2849, v2851, v2853, v2855, v2858, v2861, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2283 s i := by
  change (v3047 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v2934, v2935, v3000, v3001, v3003, v3005, v3007, v3009, v3012, v3015, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2283 s i := by
  change (v3201 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v3088, v3089, v3154, v3155, v3157, v3159, v3161, v3163, v3166, v3169, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2283 s i := by
  change (v3355 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v3242, v3243, v3308, v3309, v3311, v3313, v3315, v3317, v3320, v3323, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2283 s i := by
  change (v3509 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v3396, v3397, v3462, v3463, v3465, v3467, v3469, v3471, v3474, v3477, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2283 s i := by
  change (v3663 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v3550, v3551, v3616, v3617, v3619, v3621, v3623, v3625, v3628, v3631, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2283 s i := by
  change (v3817 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v3704, v3705, v3770, v3771, v3773, v3775, v3777, v3779, v3782, v3785, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2283 s i := by
  change (v3971 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v3858, v3859, v3924, v3925, v3927, v3929, v3931, v3933, v3936, v3939, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2283 s i := by
  change (v4125 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v4012, v4013, v4078, v4079, v4081, v4083, v4085, v4087, v4090, v4093, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2283 s i := by
  change (v4279 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v4166, v4167, v4232, v4233, v4235, v4237, v4239, v4241, v4244, v4247, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2283 s i := by
  change (v4433 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v4320, v4321, v4386, v4387, v4389, v4391, v4393, v4395, v4398, v4401, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2283 s i := by
  change (v4587 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v4474, v4475, v4540, v4541, v4543, v4545, v4547, v4549, v4552, v4555, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2283 s i := by
  change (v4705 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v4609, v4658, v4659, v4661, v4663, v4665, v4667, v4670, v4673, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2283 s i := by
  change (v4823 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v4727, v4776, v4777, v4779, v4781, v4783, v4785, v4788, v4791, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2283 s i := by
  change (v4941 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v4845, v4894, v4895, v4897, v4899, v4901, v4903, v4906, v4909, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2283 s i := by
  change (v5059 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v4963, v5012, v5013, v5015, v5017, v5019, v5021, v5024, v5027, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2283 s i := by
  change (v5177 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v5081, v5130, v5131, v5133, v5135, v5137, v5139, v5142, v5145, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2283 s i := by
  change (v5295 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v5199, v5248, v5249, v5251, v5253, v5255, v5257, v5260, v5263, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2283 s i := by
  change (v5413 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v5317, v5366, v5367, v5369, v5371, v5373, v5375, v5378, v5381, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2283 s i := by
  change (v5531 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v5435, v5484, v5485, v5487, v5489, v5491, v5493, v5496, v5499, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2283 s i := by
  change (v5649 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v5553, v5602, v5603, v5605, v5607, v5609, v5611, v5614, v5617, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2283 s i := by
  change (v5767 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v5671, v5720, v5721, v5723, v5725, v5727, v5729, v5732, v5735, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2283 s i := by
  change (v5885 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v5789, v5838, v5839, v5841, v5843, v5845, v5847, v5850, v5853, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2283 s i := by
  change (v6003 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v5907, v5956, v5957, v5959, v5961, v5963, v5965, v5968, v5971, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2283 s i := by
  change (v6121 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v6025, v6074, v6075, v6077, v6079, v6081, v6083, v6086, v6089, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2283 s i := by
  change (v6239 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v6143, v6192, v6193, v6195, v6197, v6199, v6201, v6204, v6207, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2283 s i := by
  change (v6357 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v6261, v6310, v6311, v6313, v6315, v6317, v6319, v6322, v6325, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
private theorem reference_xor_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2283 s i := by
  change (v6475 s i) = v2283 s i
  simp [v0, v1, ref_xor_v1005 s i commit known, ref_xor_v1013 s i commit known, ref_xor_v1021 s i commit known, ref_xor_v1029 s i commit known, ref_xor_v1037 s i commit known, ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, ref_xor_v1106 s i commit known, ref_xor_v1114 s i commit known, ref_xor_v1122 s i commit known, ref_xor_v1130 s i commit known, ref_xor_v1138 s i commit known, ref_xor_v1146 s i commit known, ref_xor_v1154 s i commit known, v6379, v6428, v6429, v6431, v6433, v6435, v6437, v6440, v6443, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_xor_v980 s i commit known, ref_xor_v989 s i commit known, ref_xor_v997 s i commit known, reset, target]
theorem reference_xor_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2283 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x1 s i reset commit known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x2 s i reset commit known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x3 s i reset commit known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x4 s i reset commit known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x5 s i reset commit known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x6 s i reset commit known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x7 s i reset commit known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x8 s i reset commit known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x9 s i reset commit known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x10 s i reset commit known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x11 s i reset commit known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x12 s i reset commit known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x13 s i reset commit known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x14 s i reset commit known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x15 s i reset commit known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x16 s i reset commit known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x17 s i reset commit known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x18 s i reset commit known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x19 s i reset commit known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x20 s i reset commit known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x21 s i reset commit known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x22 s i reset commit known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x23 s i reset commit known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x24 s i reset commit known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x25 s i reset commit known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x26 s i reset commit known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x27 s i reset commit known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x28 s i reset commit known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x29 s i reset commit known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x30 s i reset commit known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_xor_rd s i commit known).trans target
    rw [target]
    exact reference_xor_next_x31 s i reset commit known refTarget
#print axioms reference_xor_written_value
private theorem ref_srl_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_srl_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_srl_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v1122 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1122 s i = 0 := by
  change (if (1073762355 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v1130 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1130 s i = 0 := by
  change (if (1073741875 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v1138 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1138 s i = 1 := by
  change (if (20531 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 4261441663 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_srl_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srl_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20531 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_srl_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1046 s i commit known, ref_srl_v1052 s i commit known, ref_srl_v1058 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v1139, v1140, ref_srl_v1333 s i commit known, ref_srl_v1339 s i commit known, ref_srl_v1345 s i commit known, ref_srl_v1351 s i commit known, ref_srl_v1358 s i commit known, ref_srl_v1365 s i commit known, ref_srl_v1372 s i commit known, ref_srl_v1379 s i commit known, ref_srl_v1386 s i commit known, v1578, v1611, v1612, v1613, v1614, v1615, v1616, v1617, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_srl_rs2 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) :
    v1427 s i = BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v1139, ref_srl_v1333 s i commit known, ref_srl_v1339 s i commit known, ref_srl_v1345 s i commit known, ref_srl_v1351 s i commit known, ref_srl_v1358 s i commit known, ref_srl_v1365 s i commit known, ref_srl_v1372 s i commit known, ref_srl_v1379 s i commit known, ref_srl_v1386 s i commit known, v1392, v1407, v1408, v1409, v1410, v1411, v1412, v1413, v1414, v1415, v1416, v1417, v1418, v1419, v1420, v1421, v1422, v1423, v1424, v1425, v1426, v1427, commit, reference_commit_instruction s i commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 20+j < 25 by omega, show 20+j < 31 by omega, show 20+j < 32 by omega]
theorem reference_srl_rd (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) :
    v1320 s i = BitVec.extractLsb' 7 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1046 s i commit known, ref_srl_v1052 s i commit known, ref_srl_v1058 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v1139, v1140, v1141, v1142, v1143, v1299, v1300, v1301, v1302, v1303, v1304, v1305, v1306, v1307, v1308, v1309, v1310, v1311, v1312, v1313, v1314, v1315, v1316, v1317, v1318, v1319, v1320, commit, reference_commit_instruction s i commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega, show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 25 by omega, show 7+j < 31 by omega, show 7+j < 32 by omega]
theorem reference_srl_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_srl_rs1 s i commit known]
theorem reference_srl_operand2 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) :
    v1539 s i = referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port2 s i zero, reference_srl_rs2 s i commit known]
theorem aligned_reference_arithmetic_srl (s : State) (i : Inputs)
    (aligned : DecodedAluAligned s) (agree : RegisterAgreement s)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2271 s i := by
  have arithmetic := decoded_reference_arithmetic_srl s i s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
    s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc known
  rw [reference_srl_operand1 s i zero commit known,
    reference_srl_operand2 s i zero commit known] at arithmetic
  exact (decoded_alu_reference_operands s aligned agree).trans arithmetic
#print axioms aligned_reference_arithmetic_srl
private theorem reference_srl_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2271 s i := by
  change (v2431 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v2267, v2268, v2388, v2389, v2391, v2393, v2396, v2399, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2271 s i := by
  change (v2585 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v2468, v2469, v2542, v2543, v2545, v2547, v2550, v2553, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2271 s i := by
  change (v2739 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v2622, v2623, v2696, v2697, v2699, v2701, v2704, v2707, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2271 s i := by
  change (v2893 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v2776, v2777, v2850, v2851, v2853, v2855, v2858, v2861, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2271 s i := by
  change (v3047 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v2930, v2931, v3004, v3005, v3007, v3009, v3012, v3015, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2271 s i := by
  change (v3201 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v3084, v3085, v3158, v3159, v3161, v3163, v3166, v3169, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2271 s i := by
  change (v3355 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v3238, v3239, v3312, v3313, v3315, v3317, v3320, v3323, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2271 s i := by
  change (v3509 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v3392, v3393, v3466, v3467, v3469, v3471, v3474, v3477, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2271 s i := by
  change (v3663 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v3546, v3547, v3620, v3621, v3623, v3625, v3628, v3631, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2271 s i := by
  change (v3817 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v3700, v3701, v3774, v3775, v3777, v3779, v3782, v3785, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2271 s i := by
  change (v3971 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v3854, v3855, v3928, v3929, v3931, v3933, v3936, v3939, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2271 s i := by
  change (v4125 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v4008, v4009, v4082, v4083, v4085, v4087, v4090, v4093, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2271 s i := by
  change (v4279 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v4162, v4163, v4236, v4237, v4239, v4241, v4244, v4247, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2271 s i := by
  change (v4433 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v4316, v4317, v4390, v4391, v4393, v4395, v4398, v4401, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2271 s i := by
  change (v4587 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v4470, v4471, v4544, v4545, v4547, v4549, v4552, v4555, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2271 s i := by
  change (v4705 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v4607, v4662, v4663, v4665, v4667, v4670, v4673, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2271 s i := by
  change (v4823 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v4725, v4780, v4781, v4783, v4785, v4788, v4791, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2271 s i := by
  change (v4941 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v4843, v4898, v4899, v4901, v4903, v4906, v4909, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2271 s i := by
  change (v5059 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v4961, v5016, v5017, v5019, v5021, v5024, v5027, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2271 s i := by
  change (v5177 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v5079, v5134, v5135, v5137, v5139, v5142, v5145, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2271 s i := by
  change (v5295 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v5197, v5252, v5253, v5255, v5257, v5260, v5263, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2271 s i := by
  change (v5413 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v5315, v5370, v5371, v5373, v5375, v5378, v5381, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2271 s i := by
  change (v5531 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v5433, v5488, v5489, v5491, v5493, v5496, v5499, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2271 s i := by
  change (v5649 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v5551, v5606, v5607, v5609, v5611, v5614, v5617, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2271 s i := by
  change (v5767 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v5669, v5724, v5725, v5727, v5729, v5732, v5735, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2271 s i := by
  change (v5885 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v5787, v5842, v5843, v5845, v5847, v5850, v5853, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2271 s i := by
  change (v6003 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v5905, v5960, v5961, v5963, v5965, v5968, v5971, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2271 s i := by
  change (v6121 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v6023, v6078, v6079, v6081, v6083, v6086, v6089, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2271 s i := by
  change (v6239 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v6141, v6196, v6197, v6199, v6201, v6204, v6207, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2271 s i := by
  change (v6357 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v6259, v6314, v6315, v6317, v6319, v6322, v6325, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
private theorem reference_srl_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2271 s i := by
  change (v6475 s i) = v2271 s i
  simp [v0, v1, ref_srl_v1005 s i commit known, ref_srl_v1013 s i commit known, ref_srl_v1021 s i commit known, ref_srl_v1029 s i commit known, ref_srl_v1037 s i commit known, ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, ref_srl_v1106 s i commit known, ref_srl_v1114 s i commit known, ref_srl_v1122 s i commit known, ref_srl_v1130 s i commit known, ref_srl_v1138 s i commit known, v6377, v6432, v6433, v6435, v6437, v6440, v6443, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_srl_v980 s i commit known, ref_srl_v989 s i commit known, ref_srl_v997 s i commit known, reset, target]
theorem reference_srl_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2271 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x1 s i reset commit known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x2 s i reset commit known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x3 s i reset commit known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x4 s i reset commit known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x5 s i reset commit known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x6 s i reset commit known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x7 s i reset commit known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x8 s i reset commit known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x9 s i reset commit known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x10 s i reset commit known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x11 s i reset commit known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x12 s i reset commit known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x13 s i reset commit known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x14 s i reset commit known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x15 s i reset commit known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x16 s i reset commit known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x17 s i reset commit known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x18 s i reset commit known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x19 s i reset commit known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x20 s i reset commit known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x21 s i reset commit known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x22 s i reset commit known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x23 s i reset commit known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x24 s i reset commit known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x25 s i reset commit known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x26 s i reset commit known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x27 s i reset commit known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x28 s i reset commit known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x29 s i reset commit known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x30 s i reset commit known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_srl_rd s i commit known).trans target
    rw [target]
    exact reference_srl_next_x31 s i reset commit known refTarget
#print axioms reference_srl_written_value
private theorem ref_sra_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_sra_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_sra_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v1122 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1122 s i = 1 := by
  change (if (1073762355 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 4261441663 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_sra_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sra_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762355 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_sra_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1046 s i commit known, ref_sra_v1052 s i commit known, ref_sra_v1058 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1122 s i commit known, v1123, v1124, ref_sra_v1333 s i commit known, ref_sra_v1339 s i commit known, ref_sra_v1345 s i commit known, ref_sra_v1351 s i commit known, ref_sra_v1358 s i commit known, ref_sra_v1365 s i commit known, ref_sra_v1372 s i commit known, ref_sra_v1379 s i commit known, ref_sra_v1386 s i commit known, v1576, v1613, v1614, v1615, v1616, v1617, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_sra_rs2 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) :
    v1427 s i = BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1122 s i commit known, v1123, ref_sra_v1333 s i commit known, ref_sra_v1339 s i commit known, ref_sra_v1345 s i commit known, ref_sra_v1351 s i commit known, ref_sra_v1358 s i commit known, ref_sra_v1365 s i commit known, ref_sra_v1372 s i commit known, ref_sra_v1379 s i commit known, ref_sra_v1386 s i commit known, v1390, v1409, v1410, v1411, v1412, v1413, v1414, v1415, v1416, v1417, v1418, v1419, v1420, v1421, v1422, v1423, v1424, v1425, v1426, v1427, commit, reference_commit_instruction s i commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 20+j < 25 by omega, show 20+j < 31 by omega, show 20+j < 32 by omega]
theorem reference_sra_rd (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) :
    v1320 s i = BitVec.extractLsb' 7 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1046 s i commit known, ref_sra_v1052 s i commit known, ref_sra_v1058 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v1123, v1124, v1125, v1126, v1127, v1301, v1302, v1303, v1304, v1305, v1306, v1307, v1308, v1309, v1310, v1311, v1312, v1313, v1314, v1315, v1316, v1317, v1318, v1319, v1320, commit, reference_commit_instruction s i commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega, show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 25 by omega, show 7+j < 31 by omega, show 7+j < 32 by omega]
theorem reference_sra_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_sra_rs1 s i commit known]
theorem reference_sra_operand2 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) :
    v1539 s i = referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port2 s i zero, reference_sra_rs2 s i commit known]
theorem aligned_reference_arithmetic_sra (s : State) (i : Inputs)
    (aligned : DecodedAluAligned s) (agree : RegisterAgreement s)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2260 s i := by
  have arithmetic := decoded_reference_arithmetic_sra s i s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
    s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc known
  rw [reference_sra_operand1 s i zero commit known,
    reference_sra_operand2 s i zero commit known] at arithmetic
  exact (decoded_alu_reference_operands s aligned agree).trans arithmetic
#print axioms aligned_reference_arithmetic_sra
private theorem reference_sra_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2260 s i := by
  change (v2431 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v2256, v2257, v2392, v2393, v2396, v2399, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2260 s i := by
  change (v2585 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v2464, v2465, v2546, v2547, v2550, v2553, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2260 s i := by
  change (v2739 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v2618, v2619, v2700, v2701, v2704, v2707, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2260 s i := by
  change (v2893 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v2772, v2773, v2854, v2855, v2858, v2861, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2260 s i := by
  change (v3047 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v2926, v2927, v3008, v3009, v3012, v3015, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2260 s i := by
  change (v3201 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v3080, v3081, v3162, v3163, v3166, v3169, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2260 s i := by
  change (v3355 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v3234, v3235, v3316, v3317, v3320, v3323, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2260 s i := by
  change (v3509 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v3388, v3389, v3470, v3471, v3474, v3477, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2260 s i := by
  change (v3663 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v3542, v3543, v3624, v3625, v3628, v3631, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2260 s i := by
  change (v3817 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v3696, v3697, v3778, v3779, v3782, v3785, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2260 s i := by
  change (v3971 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v3850, v3851, v3932, v3933, v3936, v3939, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2260 s i := by
  change (v4125 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v4004, v4005, v4086, v4087, v4090, v4093, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2260 s i := by
  change (v4279 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v4158, v4159, v4240, v4241, v4244, v4247, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2260 s i := by
  change (v4433 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v4312, v4313, v4394, v4395, v4398, v4401, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2260 s i := by
  change (v4587 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v4466, v4467, v4548, v4549, v4552, v4555, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2260 s i := by
  change (v4705 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v4605, v4666, v4667, v4670, v4673, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2260 s i := by
  change (v4823 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v4723, v4784, v4785, v4788, v4791, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2260 s i := by
  change (v4941 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v4841, v4902, v4903, v4906, v4909, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2260 s i := by
  change (v5059 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v4959, v5020, v5021, v5024, v5027, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2260 s i := by
  change (v5177 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v5077, v5138, v5139, v5142, v5145, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2260 s i := by
  change (v5295 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v5195, v5256, v5257, v5260, v5263, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2260 s i := by
  change (v5413 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v5313, v5374, v5375, v5378, v5381, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2260 s i := by
  change (v5531 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v5431, v5492, v5493, v5496, v5499, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2260 s i := by
  change (v5649 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v5549, v5610, v5611, v5614, v5617, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2260 s i := by
  change (v5767 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v5667, v5728, v5729, v5732, v5735, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2260 s i := by
  change (v5885 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v5785, v5846, v5847, v5850, v5853, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2260 s i := by
  change (v6003 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v5903, v5964, v5965, v5968, v5971, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2260 s i := by
  change (v6121 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v6021, v6082, v6083, v6086, v6089, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2260 s i := by
  change (v6239 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v6139, v6200, v6201, v6204, v6207, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2260 s i := by
  change (v6357 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v6257, v6318, v6319, v6322, v6325, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
private theorem reference_sra_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2260 s i := by
  change (v6475 s i) = v2260 s i
  simp [v0, v1, ref_sra_v1005 s i commit known, ref_sra_v1013 s i commit known, ref_sra_v1021 s i commit known, ref_sra_v1029 s i commit known, ref_sra_v1037 s i commit known, ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, ref_sra_v1106 s i commit known, ref_sra_v1114 s i commit known, ref_sra_v1122 s i commit known, v6375, v6436, v6437, v6440, v6443, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_sra_v980 s i commit known, ref_sra_v989 s i commit known, ref_sra_v997 s i commit known, reset, target]
theorem reference_sra_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2260 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x1 s i reset commit known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x2 s i reset commit known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x3 s i reset commit known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x4 s i reset commit known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x5 s i reset commit known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x6 s i reset commit known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x7 s i reset commit known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x8 s i reset commit known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x9 s i reset commit known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x10 s i reset commit known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x11 s i reset commit known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x12 s i reset commit known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x13 s i reset commit known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x14 s i reset commit known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x15 s i reset commit known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x16 s i reset commit known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x17 s i reset commit known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x18 s i reset commit known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x19 s i reset commit known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x20 s i reset commit known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x21 s i reset commit known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x22 s i reset commit known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x23 s i reset commit known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x24 s i reset commit known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x25 s i reset commit known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x26 s i reset commit known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x27 s i reset commit known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x28 s i reset commit known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x29 s i reset commit known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x30 s i reset commit known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_sra_rd s i commit known).trans target
    rw [target]
    exact reference_sra_next_x31 s i reset commit known refTarget
#print axioms reference_sra_written_value
private theorem ref_or_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_or_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_or_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1122 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1122 s i = 0 := by
  change (if (1073762355 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1130 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1130 s i = 0 := by
  change (if (1073741875 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1138 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1138 s i = 0 := by
  change (if (20531 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1146 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1146 s i = 0 := by
  change (if (4147 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1154 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1154 s i = 0 := by
  change (if (16435 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1162 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1162 s i = 1 := by
  change (if (24627 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 4261441663 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_or_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_or_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 24627 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_or_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1046 s i commit known, ref_or_v1052 s i commit known, ref_or_v1058 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v1163, v1164, ref_or_v1333 s i commit known, ref_or_v1339 s i commit known, ref_or_v1345 s i commit known, ref_or_v1351 s i commit known, ref_or_v1358 s i commit known, ref_or_v1365 s i commit known, ref_or_v1372 s i commit known, ref_or_v1379 s i commit known, ref_or_v1386 s i commit known, v1581, v1608, v1609, v1610, v1611, v1612, v1613, v1614, v1615, v1616, v1617, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_or_rs2 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) :
    v1427 s i = BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v1163, ref_or_v1333 s i commit known, ref_or_v1339 s i commit known, ref_or_v1345 s i commit known, ref_or_v1351 s i commit known, ref_or_v1358 s i commit known, ref_or_v1365 s i commit known, ref_or_v1372 s i commit known, ref_or_v1379 s i commit known, ref_or_v1386 s i commit known, v1395, v1404, v1405, v1406, v1407, v1408, v1409, v1410, v1411, v1412, v1413, v1414, v1415, v1416, v1417, v1418, v1419, v1420, v1421, v1422, v1423, v1424, v1425, v1426, v1427, commit, reference_commit_instruction s i commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 20+j < 25 by omega, show 20+j < 31 by omega, show 20+j < 32 by omega]
theorem reference_or_rd (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) :
    v1320 s i = BitVec.extractLsb' 7 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1046 s i commit known, ref_or_v1052 s i commit known, ref_or_v1058 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v1163, v1164, v1165, v1166, v1167, v1296, v1297, v1298, v1299, v1300, v1301, v1302, v1303, v1304, v1305, v1306, v1307, v1308, v1309, v1310, v1311, v1312, v1313, v1314, v1315, v1316, v1317, v1318, v1319, v1320, commit, reference_commit_instruction s i commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega, show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 25 by omega, show 7+j < 31 by omega, show 7+j < 32 by omega]
theorem reference_or_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_or_rs1 s i commit known]
theorem reference_or_operand2 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) :
    v1539 s i = referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port2 s i zero, reference_or_rs2 s i commit known]
theorem aligned_reference_arithmetic_or (s : State) (i : Inputs)
    (aligned : DecodedAluAligned s) (agree : RegisterAgreement s)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2286 s i := by
  have arithmetic := decoded_reference_arithmetic_or s i s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
    s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc known
  rw [reference_or_operand1 s i zero commit known,
    reference_or_operand2 s i zero commit known] at arithmetic
  exact (decoded_alu_reference_operands s aligned agree).trans arithmetic
#print axioms aligned_reference_arithmetic_or
private theorem reference_or_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2286 s i := by
  change (v2431 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v2284, v2285, v2382, v2383, v2385, v2387, v2389, v2391, v2393, v2396, v2399, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2286 s i := by
  change (v2585 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v2474, v2475, v2536, v2537, v2539, v2541, v2543, v2545, v2547, v2550, v2553, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2286 s i := by
  change (v2739 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v2628, v2629, v2690, v2691, v2693, v2695, v2697, v2699, v2701, v2704, v2707, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2286 s i := by
  change (v2893 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v2782, v2783, v2844, v2845, v2847, v2849, v2851, v2853, v2855, v2858, v2861, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2286 s i := by
  change (v3047 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v2936, v2937, v2998, v2999, v3001, v3003, v3005, v3007, v3009, v3012, v3015, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2286 s i := by
  change (v3201 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v3090, v3091, v3152, v3153, v3155, v3157, v3159, v3161, v3163, v3166, v3169, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2286 s i := by
  change (v3355 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v3244, v3245, v3306, v3307, v3309, v3311, v3313, v3315, v3317, v3320, v3323, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2286 s i := by
  change (v3509 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v3398, v3399, v3460, v3461, v3463, v3465, v3467, v3469, v3471, v3474, v3477, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2286 s i := by
  change (v3663 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v3552, v3553, v3614, v3615, v3617, v3619, v3621, v3623, v3625, v3628, v3631, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2286 s i := by
  change (v3817 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v3706, v3707, v3768, v3769, v3771, v3773, v3775, v3777, v3779, v3782, v3785, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2286 s i := by
  change (v3971 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v3860, v3861, v3922, v3923, v3925, v3927, v3929, v3931, v3933, v3936, v3939, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2286 s i := by
  change (v4125 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v4014, v4015, v4076, v4077, v4079, v4081, v4083, v4085, v4087, v4090, v4093, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2286 s i := by
  change (v4279 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v4168, v4169, v4230, v4231, v4233, v4235, v4237, v4239, v4241, v4244, v4247, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2286 s i := by
  change (v4433 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v4322, v4323, v4384, v4385, v4387, v4389, v4391, v4393, v4395, v4398, v4401, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2286 s i := by
  change (v4587 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v4476, v4477, v4538, v4539, v4541, v4543, v4545, v4547, v4549, v4552, v4555, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2286 s i := by
  change (v4705 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v4610, v4656, v4657, v4659, v4661, v4663, v4665, v4667, v4670, v4673, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2286 s i := by
  change (v4823 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v4728, v4774, v4775, v4777, v4779, v4781, v4783, v4785, v4788, v4791, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2286 s i := by
  change (v4941 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v4846, v4892, v4893, v4895, v4897, v4899, v4901, v4903, v4906, v4909, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2286 s i := by
  change (v5059 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v4964, v5010, v5011, v5013, v5015, v5017, v5019, v5021, v5024, v5027, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2286 s i := by
  change (v5177 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v5082, v5128, v5129, v5131, v5133, v5135, v5137, v5139, v5142, v5145, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2286 s i := by
  change (v5295 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v5200, v5246, v5247, v5249, v5251, v5253, v5255, v5257, v5260, v5263, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2286 s i := by
  change (v5413 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v5318, v5364, v5365, v5367, v5369, v5371, v5373, v5375, v5378, v5381, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2286 s i := by
  change (v5531 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v5436, v5482, v5483, v5485, v5487, v5489, v5491, v5493, v5496, v5499, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2286 s i := by
  change (v5649 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v5554, v5600, v5601, v5603, v5605, v5607, v5609, v5611, v5614, v5617, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2286 s i := by
  change (v5767 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v5672, v5718, v5719, v5721, v5723, v5725, v5727, v5729, v5732, v5735, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2286 s i := by
  change (v5885 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v5790, v5836, v5837, v5839, v5841, v5843, v5845, v5847, v5850, v5853, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2286 s i := by
  change (v6003 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v5908, v5954, v5955, v5957, v5959, v5961, v5963, v5965, v5968, v5971, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2286 s i := by
  change (v6121 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v6026, v6072, v6073, v6075, v6077, v6079, v6081, v6083, v6086, v6089, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2286 s i := by
  change (v6239 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v6144, v6190, v6191, v6193, v6195, v6197, v6199, v6201, v6204, v6207, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2286 s i := by
  change (v6357 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v6262, v6308, v6309, v6311, v6313, v6315, v6317, v6319, v6322, v6325, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
private theorem reference_or_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2286 s i := by
  change (v6475 s i) = v2286 s i
  simp [v0, v1, ref_or_v1005 s i commit known, ref_or_v1013 s i commit known, ref_or_v1021 s i commit known, ref_or_v1029 s i commit known, ref_or_v1037 s i commit known, ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, ref_or_v1106 s i commit known, ref_or_v1114 s i commit known, ref_or_v1122 s i commit known, ref_or_v1130 s i commit known, ref_or_v1138 s i commit known, ref_or_v1146 s i commit known, ref_or_v1154 s i commit known, ref_or_v1162 s i commit known, v6380, v6426, v6427, v6429, v6431, v6433, v6435, v6437, v6440, v6443, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_or_v980 s i commit known, ref_or_v989 s i commit known, ref_or_v997 s i commit known, reset, target]
theorem reference_or_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2286 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x1 s i reset commit known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x2 s i reset commit known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x3 s i reset commit known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x4 s i reset commit known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x5 s i reset commit known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x6 s i reset commit known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x7 s i reset commit known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x8 s i reset commit known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x9 s i reset commit known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x10 s i reset commit known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x11 s i reset commit known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x12 s i reset commit known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x13 s i reset commit known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x14 s i reset commit known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x15 s i reset commit known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x16 s i reset commit known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x17 s i reset commit known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x18 s i reset commit known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x19 s i reset commit known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x20 s i reset commit known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x21 s i reset commit known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x22 s i reset commit known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x23 s i reset commit known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x24 s i reset commit known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x25 s i reset commit known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x26 s i reset commit known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x27 s i reset commit known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x28 s i reset commit known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x29 s i reset commit known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x30 s i reset commit known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_or_rd s i commit known).trans target
    rw [target]
    exact reference_or_next_x31 s i reset commit known refTarget
#print axioms reference_or_written_value
private theorem ref_and_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_and_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_and_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1122 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1122 s i = 0 := by
  change (if (1073762355 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1130 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1130 s i = 0 := by
  change (if (1073741875 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1138 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1138 s i = 0 := by
  change (if (20531 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1146 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1146 s i = 0 := by
  change (if (4147 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1154 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1154 s i = 0 := by
  change (if (16435 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1162 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1162 s i = 0 := by
  change (if (24627 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 4261441663 24627 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1170 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1170 s i = 1 := by
  change (if (28723 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 4261441663 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_and_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_and_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 28723 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_and_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1046 s i commit known, ref_and_v1052 s i commit known, ref_and_v1058 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v1171, v1172, ref_and_v1333 s i commit known, ref_and_v1339 s i commit known, ref_and_v1345 s i commit known, ref_and_v1351 s i commit known, ref_and_v1358 s i commit known, ref_and_v1365 s i commit known, ref_and_v1372 s i commit known, ref_and_v1379 s i commit known, ref_and_v1386 s i commit known, v1582, v1607, v1608, v1609, v1610, v1611, v1612, v1613, v1614, v1615, v1616, v1617, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_and_rs2 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) :
    v1427 s i = BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v1171, ref_and_v1333 s i commit known, ref_and_v1339 s i commit known, ref_and_v1345 s i commit known, ref_and_v1351 s i commit known, ref_and_v1358 s i commit known, ref_and_v1365 s i commit known, ref_and_v1372 s i commit known, ref_and_v1379 s i commit known, ref_and_v1386 s i commit known, v1396, v1403, v1404, v1405, v1406, v1407, v1408, v1409, v1410, v1411, v1412, v1413, v1414, v1415, v1416, v1417, v1418, v1419, v1420, v1421, v1422, v1423, v1424, v1425, v1426, v1427, commit, reference_commit_instruction s i commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 20+j < 25 by omega, show 20+j < 31 by omega, show 20+j < 32 by omega]
theorem reference_and_rd (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) :
    v1320 s i = BitVec.extractLsb' 7 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1046 s i commit known, ref_and_v1052 s i commit known, ref_and_v1058 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v1171, v1172, v1173, v1174, v1175, v1295, v1296, v1297, v1298, v1299, v1300, v1301, v1302, v1303, v1304, v1305, v1306, v1307, v1308, v1309, v1310, v1311, v1312, v1313, v1314, v1315, v1316, v1317, v1318, v1319, v1320, commit, reference_commit_instruction s i commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega, show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 25 by omega, show 7+j < 31 by omega, show 7+j < 32 by omega]
theorem reference_and_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_and_rs1 s i commit known]
theorem reference_and_operand2 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) :
    v1539 s i = referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port2 s i zero, reference_and_rs2 s i commit known]
theorem aligned_reference_arithmetic_and (s : State) (i : Inputs)
    (aligned : DecodedAluAligned s) (agree : RegisterAgreement s)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2289 s i := by
  have arithmetic := decoded_reference_arithmetic_and s i s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
    s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc known
  rw [reference_and_operand1 s i zero commit known,
    reference_and_operand2 s i zero commit known] at arithmetic
  exact (decoded_alu_reference_operands s aligned agree).trans arithmetic
#print axioms aligned_reference_arithmetic_and
private theorem reference_and_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2289 s i := by
  change (v2431 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v2287, v2288, v2380, v2381, v2383, v2385, v2387, v2389, v2391, v2393, v2396, v2399, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2289 s i := by
  change (v2585 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v2476, v2477, v2534, v2535, v2537, v2539, v2541, v2543, v2545, v2547, v2550, v2553, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2289 s i := by
  change (v2739 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v2630, v2631, v2688, v2689, v2691, v2693, v2695, v2697, v2699, v2701, v2704, v2707, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2289 s i := by
  change (v2893 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v2784, v2785, v2842, v2843, v2845, v2847, v2849, v2851, v2853, v2855, v2858, v2861, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2289 s i := by
  change (v3047 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v2938, v2939, v2996, v2997, v2999, v3001, v3003, v3005, v3007, v3009, v3012, v3015, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2289 s i := by
  change (v3201 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v3092, v3093, v3150, v3151, v3153, v3155, v3157, v3159, v3161, v3163, v3166, v3169, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2289 s i := by
  change (v3355 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v3246, v3247, v3304, v3305, v3307, v3309, v3311, v3313, v3315, v3317, v3320, v3323, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2289 s i := by
  change (v3509 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v3400, v3401, v3458, v3459, v3461, v3463, v3465, v3467, v3469, v3471, v3474, v3477, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2289 s i := by
  change (v3663 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v3554, v3555, v3612, v3613, v3615, v3617, v3619, v3621, v3623, v3625, v3628, v3631, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2289 s i := by
  change (v3817 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v3708, v3709, v3766, v3767, v3769, v3771, v3773, v3775, v3777, v3779, v3782, v3785, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2289 s i := by
  change (v3971 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v3862, v3863, v3920, v3921, v3923, v3925, v3927, v3929, v3931, v3933, v3936, v3939, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2289 s i := by
  change (v4125 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v4016, v4017, v4074, v4075, v4077, v4079, v4081, v4083, v4085, v4087, v4090, v4093, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2289 s i := by
  change (v4279 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v4170, v4171, v4228, v4229, v4231, v4233, v4235, v4237, v4239, v4241, v4244, v4247, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2289 s i := by
  change (v4433 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v4324, v4325, v4382, v4383, v4385, v4387, v4389, v4391, v4393, v4395, v4398, v4401, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2289 s i := by
  change (v4587 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v4478, v4479, v4536, v4537, v4539, v4541, v4543, v4545, v4547, v4549, v4552, v4555, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2289 s i := by
  change (v4705 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v4611, v4654, v4655, v4657, v4659, v4661, v4663, v4665, v4667, v4670, v4673, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2289 s i := by
  change (v4823 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v4729, v4772, v4773, v4775, v4777, v4779, v4781, v4783, v4785, v4788, v4791, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2289 s i := by
  change (v4941 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v4847, v4890, v4891, v4893, v4895, v4897, v4899, v4901, v4903, v4906, v4909, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2289 s i := by
  change (v5059 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v4965, v5008, v5009, v5011, v5013, v5015, v5017, v5019, v5021, v5024, v5027, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2289 s i := by
  change (v5177 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v5083, v5126, v5127, v5129, v5131, v5133, v5135, v5137, v5139, v5142, v5145, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2289 s i := by
  change (v5295 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v5201, v5244, v5245, v5247, v5249, v5251, v5253, v5255, v5257, v5260, v5263, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2289 s i := by
  change (v5413 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v5319, v5362, v5363, v5365, v5367, v5369, v5371, v5373, v5375, v5378, v5381, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2289 s i := by
  change (v5531 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v5437, v5480, v5481, v5483, v5485, v5487, v5489, v5491, v5493, v5496, v5499, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2289 s i := by
  change (v5649 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v5555, v5598, v5599, v5601, v5603, v5605, v5607, v5609, v5611, v5614, v5617, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2289 s i := by
  change (v5767 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v5673, v5716, v5717, v5719, v5721, v5723, v5725, v5727, v5729, v5732, v5735, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2289 s i := by
  change (v5885 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v5791, v5834, v5835, v5837, v5839, v5841, v5843, v5845, v5847, v5850, v5853, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2289 s i := by
  change (v6003 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v5909, v5952, v5953, v5955, v5957, v5959, v5961, v5963, v5965, v5968, v5971, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2289 s i := by
  change (v6121 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v6027, v6070, v6071, v6073, v6075, v6077, v6079, v6081, v6083, v6086, v6089, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2289 s i := by
  change (v6239 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v6145, v6188, v6189, v6191, v6193, v6195, v6197, v6199, v6201, v6204, v6207, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2289 s i := by
  change (v6357 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v6263, v6306, v6307, v6309, v6311, v6313, v6315, v6317, v6319, v6322, v6325, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
private theorem reference_and_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2289 s i := by
  change (v6475 s i) = v2289 s i
  simp [v0, v1, ref_and_v1005 s i commit known, ref_and_v1013 s i commit known, ref_and_v1021 s i commit known, ref_and_v1029 s i commit known, ref_and_v1037 s i commit known, ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, ref_and_v1106 s i commit known, ref_and_v1114 s i commit known, ref_and_v1122 s i commit known, ref_and_v1130 s i commit known, ref_and_v1138 s i commit known, ref_and_v1146 s i commit known, ref_and_v1154 s i commit known, ref_and_v1162 s i commit known, ref_and_v1170 s i commit known, v6381, v6424, v6425, v6427, v6429, v6431, v6433, v6435, v6437, v6440, v6443, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_and_v980 s i commit known, ref_and_v989 s i commit known, ref_and_v997 s i commit known, reset, target]
theorem reference_and_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2289 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x1 s i reset commit known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x2 s i reset commit known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x3 s i reset commit known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x4 s i reset commit known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x5 s i reset commit known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x6 s i reset commit known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x7 s i reset commit known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x8 s i reset commit known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x9 s i reset commit known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x10 s i reset commit known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x11 s i reset commit known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x12 s i reset commit known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x13 s i reset commit known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x14 s i reset commit known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x15 s i reset commit known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x16 s i reset commit known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x17 s i reset commit known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x18 s i reset commit known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x19 s i reset commit known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x20 s i reset commit known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x21 s i reset commit known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x22 s i reset commit known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x23 s i reset commit known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x24 s i reset commit known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x25 s i reset commit known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x26 s i reset commit known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x27 s i reset commit known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x28 s i reset commit known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x29 s i reset commit known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x30 s i reset commit known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_and_rd s i commit known).trans target
    rw [target]
    exact reference_and_next_x31 s i reset commit known refTarget
#print axioms reference_and_written_value
end RiscvMiniProofs
