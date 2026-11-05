import Proofs.ReferenceReads
import Proofs.ReferenceImmediateArithmetic
import Proofs.MaskFacts
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
private theorem reference_commit_instruction (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v977 s i = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by simp [v977, v975, v974, v973, commit]
private theorem ref_addi_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_addi_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_addi_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1122 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1122 s i = 0 := by
  change (if (1073762355 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1130 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1130 s i = 0 := by
  change (if (1073741875 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1138 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1138 s i = 0 := by
  change (if (20531 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1146 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1146 s i = 0 := by
  change (if (4147 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1154 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1154 s i = 0 := by
  change (if (16435 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1162 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1162 s i = 0 := by
  change (if (24627 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 4261441663 24627 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1170 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1170 s i = 0 := by
  change (if (28723 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 4261441663 28723 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1178 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1178 s i = 0 := by
  change (if (12339 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1186 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1186 s i = 0 := by
  change (if (8243 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1194 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1194 s i = 0 := by
  change (if (51 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1203 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1203 s i = 0 := by
  change (if (23 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1209 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1209 s i = 0 := by
  change (if (55 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1214 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1214 s i = 0 := by
  change (if (1073762323 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1221 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1221 s i = 0 := by
  change (if (20499 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1228 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1228 s i = 0 := by
  change (if (4115 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1236 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1236 s i = 0 := by
  change (if (16403 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1244 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1244 s i = 0 := by
  change (if (24595 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1252 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1252 s i = 0 := by
  change (if (28691 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1260 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1260 s i = 0 := by
  change (if (12307 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1268 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1268 s i = 0 := by
  change (if (8211 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 28799 8211 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1276 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1276 s i = 1 := by
  change (if (19 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_addi_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_addi_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 19 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_addi_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1046 s i commit known, ref_addi_v1052 s i commit known, ref_addi_v1058 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v1277, ref_addi_v1333 s i commit known, ref_addi_v1339 s i commit known, ref_addi_v1345 s i commit known, ref_addi_v1351 s i commit known, ref_addi_v1358 s i commit known, ref_addi_v1365 s i commit known, ref_addi_v1372 s i commit known, ref_addi_v1379 s i commit known, ref_addi_v1386 s i commit known, v1594, v1595, v1596, v1597, v1598, v1599, v1600, v1601, v1602, v1603, v1604, v1605, v1606, v1607, v1608, v1609, v1610, v1611, v1612, v1613, v1614, v1615, v1616, v1617, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_addi_rd (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) :
    v1320 s i = BitVec.extractLsb' 7 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1046 s i commit known, ref_addi_v1052 s i commit known, ref_addi_v1058 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v1277, v1278, v1279, v1280, v1281, v1282, v1283, v1284, v1285, v1286, v1287, v1288, v1289, v1290, v1291, v1292, v1293, v1294, v1295, v1296, v1297, v1298, v1299, v1300, v1301, v1302, v1303, v1304, v1305, v1306, v1307, v1308, v1309, v1310, v1311, v1312, v1313, v1314, v1315, v1316, v1317, v1318, v1319, v1320, commit, reference_commit_instruction s i commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega, show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 25 by omega, show 7+j < 31 by omega, show 7+j < 32 by omega]
theorem reference_addi_immediate (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) : v2092 s i = immediateI s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_addi_v1046 s i commit known, ref_addi_v1052 s i commit known, ref_addi_v1058 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, ref_addi_v1333 s i commit known, ref_addi_v1339 s i commit known, ref_addi_v1345 s i commit known, ref_addi_v1351 s i commit known, ref_addi_v1358 s i commit known, ref_addi_v1365 s i commit known, ref_addi_v1372 s i commit known, ref_addi_v1379 s i commit known, ref_addi_v1386 s i commit known, v1809, v1811, v1812, v1813, v1814, v1815, v1816, v1817, v1818, v1819, v1820, v1821, v1822, v1823, v1824, v1825, v1826, v1827, v1828, v1829, v1831, v1832, v2059, v2060, v2061, v2062, v2063, v2064, v2065, v2066, v2067, v2068, v2069, v2070, v2071, v2072, v2073, v2074, v2075, v2076, v2077, v2078, v2079, v2080, v2081, v2082, v2083, v2084, v2085, v2086, v2087, v2088, v2089, v2090, v2091, v2092, commit, reference_commit_instruction s i commit, BitVec.reduceEq, if_true, if_false]
  rw [reference_sign_extension]
  rfl
theorem reference_addi_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_addi_rs1 s i commit known]
theorem aligned_reference_arithmetic_addi (s : State) (i : Inputs)
    (aligned : DecodedAluAligned s) (agree : RegisterAgreement s)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2351 s i := by
  have arithmetic := decoded_reference_immediate_addi s i s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
    s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc (referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst)) known
    (reference_addi_immediate s i commit known)
  rw [reference_addi_operand1 s i zero commit known] at arithmetic
  exact (decoded_alu_reference_operands s aligned agree).trans arithmetic
#print axioms aligned_reference_arithmetic_addi
private theorem reference_addi_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2351 s i := by
  change (v2431 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v2346, v2347, v2352, v2353, v2355, v2357, v2359, v2361, v2363, v2365, v2367, v2369, v2371, v2373, v2375, v2377, v2379, v2381, v2383, v2385, v2387, v2389, v2391, v2393, v2396, v2399, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2351 s i := by
  change (v2585 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v2504, v2505, v2506, v2507, v2509, v2511, v2513, v2515, v2517, v2519, v2521, v2523, v2525, v2527, v2529, v2531, v2533, v2535, v2537, v2539, v2541, v2543, v2545, v2547, v2550, v2553, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2351 s i := by
  change (v2739 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v2658, v2659, v2660, v2661, v2663, v2665, v2667, v2669, v2671, v2673, v2675, v2677, v2679, v2681, v2683, v2685, v2687, v2689, v2691, v2693, v2695, v2697, v2699, v2701, v2704, v2707, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2351 s i := by
  change (v2893 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v2812, v2813, v2814, v2815, v2817, v2819, v2821, v2823, v2825, v2827, v2829, v2831, v2833, v2835, v2837, v2839, v2841, v2843, v2845, v2847, v2849, v2851, v2853, v2855, v2858, v2861, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2351 s i := by
  change (v3047 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v2966, v2967, v2968, v2969, v2971, v2973, v2975, v2977, v2979, v2981, v2983, v2985, v2987, v2989, v2991, v2993, v2995, v2997, v2999, v3001, v3003, v3005, v3007, v3009, v3012, v3015, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2351 s i := by
  change (v3201 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v3120, v3121, v3122, v3123, v3125, v3127, v3129, v3131, v3133, v3135, v3137, v3139, v3141, v3143, v3145, v3147, v3149, v3151, v3153, v3155, v3157, v3159, v3161, v3163, v3166, v3169, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2351 s i := by
  change (v3355 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v3274, v3275, v3276, v3277, v3279, v3281, v3283, v3285, v3287, v3289, v3291, v3293, v3295, v3297, v3299, v3301, v3303, v3305, v3307, v3309, v3311, v3313, v3315, v3317, v3320, v3323, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2351 s i := by
  change (v3509 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v3428, v3429, v3430, v3431, v3433, v3435, v3437, v3439, v3441, v3443, v3445, v3447, v3449, v3451, v3453, v3455, v3457, v3459, v3461, v3463, v3465, v3467, v3469, v3471, v3474, v3477, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2351 s i := by
  change (v3663 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v3582, v3583, v3584, v3585, v3587, v3589, v3591, v3593, v3595, v3597, v3599, v3601, v3603, v3605, v3607, v3609, v3611, v3613, v3615, v3617, v3619, v3621, v3623, v3625, v3628, v3631, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2351 s i := by
  change (v3817 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v3736, v3737, v3738, v3739, v3741, v3743, v3745, v3747, v3749, v3751, v3753, v3755, v3757, v3759, v3761, v3763, v3765, v3767, v3769, v3771, v3773, v3775, v3777, v3779, v3782, v3785, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2351 s i := by
  change (v3971 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v3890, v3891, v3892, v3893, v3895, v3897, v3899, v3901, v3903, v3905, v3907, v3909, v3911, v3913, v3915, v3917, v3919, v3921, v3923, v3925, v3927, v3929, v3931, v3933, v3936, v3939, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2351 s i := by
  change (v4125 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v4044, v4045, v4046, v4047, v4049, v4051, v4053, v4055, v4057, v4059, v4061, v4063, v4065, v4067, v4069, v4071, v4073, v4075, v4077, v4079, v4081, v4083, v4085, v4087, v4090, v4093, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2351 s i := by
  change (v4279 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v4198, v4199, v4200, v4201, v4203, v4205, v4207, v4209, v4211, v4213, v4215, v4217, v4219, v4221, v4223, v4225, v4227, v4229, v4231, v4233, v4235, v4237, v4239, v4241, v4244, v4247, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2351 s i := by
  change (v4433 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v4352, v4353, v4354, v4355, v4357, v4359, v4361, v4363, v4365, v4367, v4369, v4371, v4373, v4375, v4377, v4379, v4381, v4383, v4385, v4387, v4389, v4391, v4393, v4395, v4398, v4401, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2351 s i := by
  change (v4587 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v4506, v4507, v4508, v4509, v4511, v4513, v4515, v4517, v4519, v4521, v4523, v4525, v4527, v4529, v4531, v4533, v4535, v4537, v4539, v4541, v4543, v4545, v4547, v4549, v4552, v4555, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2351 s i := by
  change (v4705 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v4625, v4626, v4627, v4629, v4631, v4633, v4635, v4637, v4639, v4641, v4643, v4645, v4647, v4649, v4651, v4653, v4655, v4657, v4659, v4661, v4663, v4665, v4667, v4670, v4673, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2351 s i := by
  change (v4823 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v4743, v4744, v4745, v4747, v4749, v4751, v4753, v4755, v4757, v4759, v4761, v4763, v4765, v4767, v4769, v4771, v4773, v4775, v4777, v4779, v4781, v4783, v4785, v4788, v4791, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2351 s i := by
  change (v4941 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v4861, v4862, v4863, v4865, v4867, v4869, v4871, v4873, v4875, v4877, v4879, v4881, v4883, v4885, v4887, v4889, v4891, v4893, v4895, v4897, v4899, v4901, v4903, v4906, v4909, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2351 s i := by
  change (v5059 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v4979, v4980, v4981, v4983, v4985, v4987, v4989, v4991, v4993, v4995, v4997, v4999, v5001, v5003, v5005, v5007, v5009, v5011, v5013, v5015, v5017, v5019, v5021, v5024, v5027, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2351 s i := by
  change (v5177 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v5097, v5098, v5099, v5101, v5103, v5105, v5107, v5109, v5111, v5113, v5115, v5117, v5119, v5121, v5123, v5125, v5127, v5129, v5131, v5133, v5135, v5137, v5139, v5142, v5145, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2351 s i := by
  change (v5295 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v5215, v5216, v5217, v5219, v5221, v5223, v5225, v5227, v5229, v5231, v5233, v5235, v5237, v5239, v5241, v5243, v5245, v5247, v5249, v5251, v5253, v5255, v5257, v5260, v5263, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2351 s i := by
  change (v5413 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v5333, v5334, v5335, v5337, v5339, v5341, v5343, v5345, v5347, v5349, v5351, v5353, v5355, v5357, v5359, v5361, v5363, v5365, v5367, v5369, v5371, v5373, v5375, v5378, v5381, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2351 s i := by
  change (v5531 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v5451, v5452, v5453, v5455, v5457, v5459, v5461, v5463, v5465, v5467, v5469, v5471, v5473, v5475, v5477, v5479, v5481, v5483, v5485, v5487, v5489, v5491, v5493, v5496, v5499, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2351 s i := by
  change (v5649 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v5569, v5570, v5571, v5573, v5575, v5577, v5579, v5581, v5583, v5585, v5587, v5589, v5591, v5593, v5595, v5597, v5599, v5601, v5603, v5605, v5607, v5609, v5611, v5614, v5617, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2351 s i := by
  change (v5767 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v5687, v5688, v5689, v5691, v5693, v5695, v5697, v5699, v5701, v5703, v5705, v5707, v5709, v5711, v5713, v5715, v5717, v5719, v5721, v5723, v5725, v5727, v5729, v5732, v5735, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2351 s i := by
  change (v5885 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v5805, v5806, v5807, v5809, v5811, v5813, v5815, v5817, v5819, v5821, v5823, v5825, v5827, v5829, v5831, v5833, v5835, v5837, v5839, v5841, v5843, v5845, v5847, v5850, v5853, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2351 s i := by
  change (v6003 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v5923, v5924, v5925, v5927, v5929, v5931, v5933, v5935, v5937, v5939, v5941, v5943, v5945, v5947, v5949, v5951, v5953, v5955, v5957, v5959, v5961, v5963, v5965, v5968, v5971, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2351 s i := by
  change (v6121 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v6041, v6042, v6043, v6045, v6047, v6049, v6051, v6053, v6055, v6057, v6059, v6061, v6063, v6065, v6067, v6069, v6071, v6073, v6075, v6077, v6079, v6081, v6083, v6086, v6089, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2351 s i := by
  change (v6239 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v6159, v6160, v6161, v6163, v6165, v6167, v6169, v6171, v6173, v6175, v6177, v6179, v6181, v6183, v6185, v6187, v6189, v6191, v6193, v6195, v6197, v6199, v6201, v6204, v6207, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2351 s i := by
  change (v6357 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v6277, v6278, v6279, v6281, v6283, v6285, v6287, v6289, v6291, v6293, v6295, v6297, v6299, v6301, v6303, v6305, v6307, v6309, v6311, v6313, v6315, v6317, v6319, v6322, v6325, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
private theorem reference_addi_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2351 s i := by
  change (v6475 s i) = v2351 s i
  simp [v0, v1, ref_addi_v1005 s i commit known, ref_addi_v1013 s i commit known, ref_addi_v1021 s i commit known, ref_addi_v1029 s i commit known, ref_addi_v1037 s i commit known, ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, ref_addi_v1106 s i commit known, ref_addi_v1114 s i commit known, ref_addi_v1122 s i commit known, ref_addi_v1130 s i commit known, ref_addi_v1138 s i commit known, ref_addi_v1146 s i commit known, ref_addi_v1154 s i commit known, ref_addi_v1162 s i commit known, ref_addi_v1170 s i commit known, ref_addi_v1178 s i commit known, ref_addi_v1186 s i commit known, ref_addi_v1194 s i commit known, ref_addi_v1203 s i commit known, ref_addi_v1209 s i commit known, ref_addi_v1214 s i commit known, ref_addi_v1221 s i commit known, ref_addi_v1228 s i commit known, ref_addi_v1236 s i commit known, ref_addi_v1244 s i commit known, ref_addi_v1252 s i commit known, ref_addi_v1260 s i commit known, ref_addi_v1268 s i commit known, ref_addi_v1276 s i commit known, v6395, v6396, v6397, v6399, v6401, v6403, v6405, v6407, v6409, v6411, v6413, v6415, v6417, v6419, v6421, v6423, v6425, v6427, v6429, v6431, v6433, v6435, v6437, v6440, v6443, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_addi_v980 s i commit known, ref_addi_v989 s i commit known, ref_addi_v997 s i commit known, reset, target]
theorem reference_addi_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2351 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x1 s i reset commit known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x2 s i reset commit known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x3 s i reset commit known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x4 s i reset commit known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x5 s i reset commit known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x6 s i reset commit known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x7 s i reset commit known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x8 s i reset commit known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x9 s i reset commit known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x10 s i reset commit known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x11 s i reset commit known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x12 s i reset commit known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x13 s i reset commit known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x14 s i reset commit known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x15 s i reset commit known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x16 s i reset commit known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x17 s i reset commit known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x18 s i reset commit known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x19 s i reset commit known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x20 s i reset commit known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x21 s i reset commit known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x22 s i reset commit known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x23 s i reset commit known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x24 s i reset commit known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x25 s i reset commit known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x26 s i reset commit known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x27 s i reset commit known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x28 s i reset commit known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x29 s i reset commit known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x30 s i reset commit known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_addi_rd s i commit known).trans target
    rw [target]
    exact reference_addi_next_x31 s i reset commit known refTarget
#print axioms reference_addi_written_value
private theorem ref_slti_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_slti_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_slti_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1122 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1122 s i = 0 := by
  change (if (1073762355 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1130 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1130 s i = 0 := by
  change (if (1073741875 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1138 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1138 s i = 0 := by
  change (if (20531 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1146 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1146 s i = 0 := by
  change (if (4147 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1154 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1154 s i = 0 := by
  change (if (16435 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1162 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1162 s i = 0 := by
  change (if (24627 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 4261441663 24627 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1170 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1170 s i = 0 := by
  change (if (28723 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 4261441663 28723 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1178 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1178 s i = 0 := by
  change (if (12339 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1186 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1186 s i = 0 := by
  change (if (8243 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1194 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1194 s i = 0 := by
  change (if (51 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1203 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1203 s i = 0 := by
  change (if (23 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1209 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1209 s i = 0 := by
  change (if (55 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1214 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1214 s i = 0 := by
  change (if (1073762323 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1221 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1221 s i = 0 := by
  change (if (20499 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1228 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1228 s i = 0 := by
  change (if (4115 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1236 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1236 s i = 0 := by
  change (if (16403 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1244 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1244 s i = 0 := by
  change (if (24595 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1252 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1252 s i = 0 := by
  change (if (28691 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1260 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1260 s i = 0 := by
  change (if (12307 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 28799 12307 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1268 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1268 s i = 1 := by
  change (if (8211 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_slti_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slti_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8211 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_slti_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1046 s i commit known, ref_slti_v1052 s i commit known, ref_slti_v1058 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v1269, ref_slti_v1333 s i commit known, ref_slti_v1339 s i commit known, ref_slti_v1345 s i commit known, ref_slti_v1351 s i commit known, ref_slti_v1358 s i commit known, ref_slti_v1365 s i commit known, ref_slti_v1372 s i commit known, ref_slti_v1379 s i commit known, ref_slti_v1386 s i commit known, v1593, v1596, v1597, v1598, v1599, v1600, v1601, v1602, v1603, v1604, v1605, v1606, v1607, v1608, v1609, v1610, v1611, v1612, v1613, v1614, v1615, v1616, v1617, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_slti_rd (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) :
    v1320 s i = BitVec.extractLsb' 7 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1046 s i commit known, ref_slti_v1052 s i commit known, ref_slti_v1058 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v1269, v1270, v1271, v1272, v1282, v1283, v1284, v1285, v1286, v1287, v1288, v1289, v1290, v1291, v1292, v1293, v1294, v1295, v1296, v1297, v1298, v1299, v1300, v1301, v1302, v1303, v1304, v1305, v1306, v1307, v1308, v1309, v1310, v1311, v1312, v1313, v1314, v1315, v1316, v1317, v1318, v1319, v1320, commit, reference_commit_instruction s i commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega, show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 25 by omega, show 7+j < 31 by omega, show 7+j < 32 by omega]
theorem reference_slti_immediate (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) : v2092 s i = immediateI s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_slti_v1046 s i commit known, ref_slti_v1052 s i commit known, ref_slti_v1058 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, ref_slti_v1333 s i commit known, ref_slti_v1339 s i commit known, ref_slti_v1345 s i commit known, ref_slti_v1351 s i commit known, ref_slti_v1358 s i commit known, ref_slti_v1365 s i commit known, ref_slti_v1372 s i commit known, ref_slti_v1379 s i commit known, ref_slti_v1386 s i commit known, v1808, v1812, v1813, v1814, v1815, v1816, v1817, v1818, v1819, v1820, v1821, v1822, v1823, v1824, v1825, v1826, v1827, v1828, v1829, v1831, v1832, v2056, v2057, v2058, v2063, v2064, v2065, v2066, v2067, v2068, v2069, v2070, v2071, v2072, v2073, v2074, v2075, v2076, v2077, v2078, v2079, v2080, v2081, v2082, v2083, v2084, v2085, v2086, v2087, v2088, v2089, v2090, v2091, v2092, commit, reference_commit_instruction s i commit, BitVec.reduceEq, if_true, if_false]
  rw [reference_sign_extension]
  rfl
theorem reference_slti_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_slti_rs1 s i commit known]
theorem aligned_reference_arithmetic_slti (s : State) (i : Inputs)
    (aligned : DecodedAluAligned s) (agree : RegisterAgreement s)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2345 s i := by
  have arithmetic := decoded_reference_immediate_slti s i s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
    s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc (referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst)) known
    (reference_slti_immediate s i commit known)
  rw [reference_slti_operand1 s i zero commit known] at arithmetic
  exact (decoded_alu_reference_operands s aligned agree).trans arithmetic
#print axioms aligned_reference_arithmetic_slti
private theorem reference_slti_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2345 s i := by
  change (v2431 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v2342, v2343, v2354, v2355, v2357, v2359, v2361, v2363, v2365, v2367, v2369, v2371, v2373, v2375, v2377, v2379, v2381, v2383, v2385, v2387, v2389, v2391, v2393, v2396, v2399, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2345 s i := by
  change (v2585 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v2502, v2503, v2508, v2509, v2511, v2513, v2515, v2517, v2519, v2521, v2523, v2525, v2527, v2529, v2531, v2533, v2535, v2537, v2539, v2541, v2543, v2545, v2547, v2550, v2553, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2345 s i := by
  change (v2739 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v2656, v2657, v2662, v2663, v2665, v2667, v2669, v2671, v2673, v2675, v2677, v2679, v2681, v2683, v2685, v2687, v2689, v2691, v2693, v2695, v2697, v2699, v2701, v2704, v2707, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2345 s i := by
  change (v2893 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v2810, v2811, v2816, v2817, v2819, v2821, v2823, v2825, v2827, v2829, v2831, v2833, v2835, v2837, v2839, v2841, v2843, v2845, v2847, v2849, v2851, v2853, v2855, v2858, v2861, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2345 s i := by
  change (v3047 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v2964, v2965, v2970, v2971, v2973, v2975, v2977, v2979, v2981, v2983, v2985, v2987, v2989, v2991, v2993, v2995, v2997, v2999, v3001, v3003, v3005, v3007, v3009, v3012, v3015, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2345 s i := by
  change (v3201 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v3118, v3119, v3124, v3125, v3127, v3129, v3131, v3133, v3135, v3137, v3139, v3141, v3143, v3145, v3147, v3149, v3151, v3153, v3155, v3157, v3159, v3161, v3163, v3166, v3169, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2345 s i := by
  change (v3355 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v3272, v3273, v3278, v3279, v3281, v3283, v3285, v3287, v3289, v3291, v3293, v3295, v3297, v3299, v3301, v3303, v3305, v3307, v3309, v3311, v3313, v3315, v3317, v3320, v3323, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2345 s i := by
  change (v3509 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v3426, v3427, v3432, v3433, v3435, v3437, v3439, v3441, v3443, v3445, v3447, v3449, v3451, v3453, v3455, v3457, v3459, v3461, v3463, v3465, v3467, v3469, v3471, v3474, v3477, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2345 s i := by
  change (v3663 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v3580, v3581, v3586, v3587, v3589, v3591, v3593, v3595, v3597, v3599, v3601, v3603, v3605, v3607, v3609, v3611, v3613, v3615, v3617, v3619, v3621, v3623, v3625, v3628, v3631, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2345 s i := by
  change (v3817 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v3734, v3735, v3740, v3741, v3743, v3745, v3747, v3749, v3751, v3753, v3755, v3757, v3759, v3761, v3763, v3765, v3767, v3769, v3771, v3773, v3775, v3777, v3779, v3782, v3785, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2345 s i := by
  change (v3971 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v3888, v3889, v3894, v3895, v3897, v3899, v3901, v3903, v3905, v3907, v3909, v3911, v3913, v3915, v3917, v3919, v3921, v3923, v3925, v3927, v3929, v3931, v3933, v3936, v3939, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2345 s i := by
  change (v4125 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v4042, v4043, v4048, v4049, v4051, v4053, v4055, v4057, v4059, v4061, v4063, v4065, v4067, v4069, v4071, v4073, v4075, v4077, v4079, v4081, v4083, v4085, v4087, v4090, v4093, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2345 s i := by
  change (v4279 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v4196, v4197, v4202, v4203, v4205, v4207, v4209, v4211, v4213, v4215, v4217, v4219, v4221, v4223, v4225, v4227, v4229, v4231, v4233, v4235, v4237, v4239, v4241, v4244, v4247, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2345 s i := by
  change (v4433 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v4350, v4351, v4356, v4357, v4359, v4361, v4363, v4365, v4367, v4369, v4371, v4373, v4375, v4377, v4379, v4381, v4383, v4385, v4387, v4389, v4391, v4393, v4395, v4398, v4401, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2345 s i := by
  change (v4587 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v4504, v4505, v4510, v4511, v4513, v4515, v4517, v4519, v4521, v4523, v4525, v4527, v4529, v4531, v4533, v4535, v4537, v4539, v4541, v4543, v4545, v4547, v4549, v4552, v4555, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2345 s i := by
  change (v4705 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v4624, v4628, v4629, v4631, v4633, v4635, v4637, v4639, v4641, v4643, v4645, v4647, v4649, v4651, v4653, v4655, v4657, v4659, v4661, v4663, v4665, v4667, v4670, v4673, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2345 s i := by
  change (v4823 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v4742, v4746, v4747, v4749, v4751, v4753, v4755, v4757, v4759, v4761, v4763, v4765, v4767, v4769, v4771, v4773, v4775, v4777, v4779, v4781, v4783, v4785, v4788, v4791, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2345 s i := by
  change (v4941 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v4860, v4864, v4865, v4867, v4869, v4871, v4873, v4875, v4877, v4879, v4881, v4883, v4885, v4887, v4889, v4891, v4893, v4895, v4897, v4899, v4901, v4903, v4906, v4909, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2345 s i := by
  change (v5059 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v4978, v4982, v4983, v4985, v4987, v4989, v4991, v4993, v4995, v4997, v4999, v5001, v5003, v5005, v5007, v5009, v5011, v5013, v5015, v5017, v5019, v5021, v5024, v5027, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2345 s i := by
  change (v5177 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v5096, v5100, v5101, v5103, v5105, v5107, v5109, v5111, v5113, v5115, v5117, v5119, v5121, v5123, v5125, v5127, v5129, v5131, v5133, v5135, v5137, v5139, v5142, v5145, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2345 s i := by
  change (v5295 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v5214, v5218, v5219, v5221, v5223, v5225, v5227, v5229, v5231, v5233, v5235, v5237, v5239, v5241, v5243, v5245, v5247, v5249, v5251, v5253, v5255, v5257, v5260, v5263, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2345 s i := by
  change (v5413 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v5332, v5336, v5337, v5339, v5341, v5343, v5345, v5347, v5349, v5351, v5353, v5355, v5357, v5359, v5361, v5363, v5365, v5367, v5369, v5371, v5373, v5375, v5378, v5381, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2345 s i := by
  change (v5531 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v5450, v5454, v5455, v5457, v5459, v5461, v5463, v5465, v5467, v5469, v5471, v5473, v5475, v5477, v5479, v5481, v5483, v5485, v5487, v5489, v5491, v5493, v5496, v5499, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2345 s i := by
  change (v5649 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v5568, v5572, v5573, v5575, v5577, v5579, v5581, v5583, v5585, v5587, v5589, v5591, v5593, v5595, v5597, v5599, v5601, v5603, v5605, v5607, v5609, v5611, v5614, v5617, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2345 s i := by
  change (v5767 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v5686, v5690, v5691, v5693, v5695, v5697, v5699, v5701, v5703, v5705, v5707, v5709, v5711, v5713, v5715, v5717, v5719, v5721, v5723, v5725, v5727, v5729, v5732, v5735, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2345 s i := by
  change (v5885 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v5804, v5808, v5809, v5811, v5813, v5815, v5817, v5819, v5821, v5823, v5825, v5827, v5829, v5831, v5833, v5835, v5837, v5839, v5841, v5843, v5845, v5847, v5850, v5853, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2345 s i := by
  change (v6003 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v5922, v5926, v5927, v5929, v5931, v5933, v5935, v5937, v5939, v5941, v5943, v5945, v5947, v5949, v5951, v5953, v5955, v5957, v5959, v5961, v5963, v5965, v5968, v5971, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2345 s i := by
  change (v6121 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v6040, v6044, v6045, v6047, v6049, v6051, v6053, v6055, v6057, v6059, v6061, v6063, v6065, v6067, v6069, v6071, v6073, v6075, v6077, v6079, v6081, v6083, v6086, v6089, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2345 s i := by
  change (v6239 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v6158, v6162, v6163, v6165, v6167, v6169, v6171, v6173, v6175, v6177, v6179, v6181, v6183, v6185, v6187, v6189, v6191, v6193, v6195, v6197, v6199, v6201, v6204, v6207, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2345 s i := by
  change (v6357 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v6276, v6280, v6281, v6283, v6285, v6287, v6289, v6291, v6293, v6295, v6297, v6299, v6301, v6303, v6305, v6307, v6309, v6311, v6313, v6315, v6317, v6319, v6322, v6325, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
private theorem reference_slti_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2345 s i := by
  change (v6475 s i) = v2345 s i
  simp [v0, v1, ref_slti_v1005 s i commit known, ref_slti_v1013 s i commit known, ref_slti_v1021 s i commit known, ref_slti_v1029 s i commit known, ref_slti_v1037 s i commit known, ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, ref_slti_v1106 s i commit known, ref_slti_v1114 s i commit known, ref_slti_v1122 s i commit known, ref_slti_v1130 s i commit known, ref_slti_v1138 s i commit known, ref_slti_v1146 s i commit known, ref_slti_v1154 s i commit known, ref_slti_v1162 s i commit known, ref_slti_v1170 s i commit known, ref_slti_v1178 s i commit known, ref_slti_v1186 s i commit known, ref_slti_v1194 s i commit known, ref_slti_v1203 s i commit known, ref_slti_v1209 s i commit known, ref_slti_v1214 s i commit known, ref_slti_v1221 s i commit known, ref_slti_v1228 s i commit known, ref_slti_v1236 s i commit known, ref_slti_v1244 s i commit known, ref_slti_v1252 s i commit known, ref_slti_v1260 s i commit known, ref_slti_v1268 s i commit known, v6394, v6398, v6399, v6401, v6403, v6405, v6407, v6409, v6411, v6413, v6415, v6417, v6419, v6421, v6423, v6425, v6427, v6429, v6431, v6433, v6435, v6437, v6440, v6443, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_slti_v980 s i commit known, ref_slti_v989 s i commit known, ref_slti_v997 s i commit known, reset, target]
theorem reference_slti_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2345 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x1 s i reset commit known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x2 s i reset commit known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x3 s i reset commit known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x4 s i reset commit known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x5 s i reset commit known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x6 s i reset commit known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x7 s i reset commit known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x8 s i reset commit known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x9 s i reset commit known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x10 s i reset commit known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x11 s i reset commit known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x12 s i reset commit known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x13 s i reset commit known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x14 s i reset commit known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x15 s i reset commit known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x16 s i reset commit known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x17 s i reset commit known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x18 s i reset commit known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x19 s i reset commit known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x20 s i reset commit known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x21 s i reset commit known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x22 s i reset commit known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x23 s i reset commit known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x24 s i reset commit known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x25 s i reset commit known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x26 s i reset commit known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x27 s i reset commit known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x28 s i reset commit known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x29 s i reset commit known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x30 s i reset commit known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_slti_rd s i commit known).trans target
    rw [target]
    exact reference_slti_next_x31 s i reset commit known refTarget
#print axioms reference_slti_written_value
private theorem ref_sltiu_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_sltiu_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_sltiu_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1122 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1122 s i = 0 := by
  change (if (1073762355 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1130 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1130 s i = 0 := by
  change (if (1073741875 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1138 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1138 s i = 0 := by
  change (if (20531 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1146 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1146 s i = 0 := by
  change (if (4147 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1154 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1154 s i = 0 := by
  change (if (16435 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1162 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1162 s i = 0 := by
  change (if (24627 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 4261441663 24627 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1170 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1170 s i = 0 := by
  change (if (28723 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 4261441663 28723 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1178 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1178 s i = 0 := by
  change (if (12339 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1186 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1186 s i = 0 := by
  change (if (8243 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1194 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1194 s i = 0 := by
  change (if (51 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1203 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1203 s i = 0 := by
  change (if (23 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1209 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1209 s i = 0 := by
  change (if (55 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1214 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1214 s i = 0 := by
  change (if (1073762323 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1221 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1221 s i = 0 := by
  change (if (20499 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1228 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1228 s i = 0 := by
  change (if (4115 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1236 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1236 s i = 0 := by
  change (if (16403 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1244 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1244 s i = 0 := by
  change (if (24595 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1252 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1252 s i = 0 := by
  change (if (28691 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 28799 28691 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1260 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1260 s i = 1 := by
  change (if (12307 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_sltiu_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sltiu_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 12307 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_sltiu_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1046 s i commit known, ref_sltiu_v1052 s i commit known, ref_sltiu_v1058 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v1261, ref_sltiu_v1333 s i commit known, ref_sltiu_v1339 s i commit known, ref_sltiu_v1345 s i commit known, ref_sltiu_v1351 s i commit known, ref_sltiu_v1358 s i commit known, ref_sltiu_v1365 s i commit known, ref_sltiu_v1372 s i commit known, ref_sltiu_v1379 s i commit known, ref_sltiu_v1386 s i commit known, v1592, v1597, v1598, v1599, v1600, v1601, v1602, v1603, v1604, v1605, v1606, v1607, v1608, v1609, v1610, v1611, v1612, v1613, v1614, v1615, v1616, v1617, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_sltiu_rd (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) :
    v1320 s i = BitVec.extractLsb' 7 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1046 s i commit known, ref_sltiu_v1052 s i commit known, ref_sltiu_v1058 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v1261, v1262, v1263, v1264, v1283, v1284, v1285, v1286, v1287, v1288, v1289, v1290, v1291, v1292, v1293, v1294, v1295, v1296, v1297, v1298, v1299, v1300, v1301, v1302, v1303, v1304, v1305, v1306, v1307, v1308, v1309, v1310, v1311, v1312, v1313, v1314, v1315, v1316, v1317, v1318, v1319, v1320, commit, reference_commit_instruction s i commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega, show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 25 by omega, show 7+j < 31 by omega, show 7+j < 32 by omega]
theorem reference_sltiu_immediate (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) : v2092 s i = immediateI s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sltiu_v1046 s i commit known, ref_sltiu_v1052 s i commit known, ref_sltiu_v1058 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, ref_sltiu_v1333 s i commit known, ref_sltiu_v1339 s i commit known, ref_sltiu_v1345 s i commit known, ref_sltiu_v1351 s i commit known, ref_sltiu_v1358 s i commit known, ref_sltiu_v1365 s i commit known, ref_sltiu_v1372 s i commit known, ref_sltiu_v1379 s i commit known, ref_sltiu_v1386 s i commit known, v1807, v1813, v1814, v1815, v1816, v1817, v1818, v1819, v1820, v1821, v1822, v1823, v1824, v1825, v1826, v1827, v1828, v1829, v1831, v1832, v2053, v2054, v2055, v2064, v2065, v2066, v2067, v2068, v2069, v2070, v2071, v2072, v2073, v2074, v2075, v2076, v2077, v2078, v2079, v2080, v2081, v2082, v2083, v2084, v2085, v2086, v2087, v2088, v2089, v2090, v2091, v2092, commit, reference_commit_instruction s i commit, BitVec.reduceEq, if_true, if_false]
  rw [reference_sign_extension]
  rfl
theorem reference_sltiu_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_sltiu_rs1 s i commit known]
theorem aligned_reference_arithmetic_sltiu (s : State) (i : Inputs)
    (aligned : DecodedAluAligned s) (agree : RegisterAgreement s)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2341 s i := by
  have arithmetic := decoded_reference_immediate_sltiu s i s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
    s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc (referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst)) known
    (reference_sltiu_immediate s i commit known)
  rw [reference_sltiu_operand1 s i zero commit known] at arithmetic
  exact (decoded_alu_reference_operands s aligned agree).trans arithmetic
#print axioms aligned_reference_arithmetic_sltiu
private theorem reference_sltiu_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2341 s i := by
  change (v2431 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v2338, v2339, v2356, v2357, v2359, v2361, v2363, v2365, v2367, v2369, v2371, v2373, v2375, v2377, v2379, v2381, v2383, v2385, v2387, v2389, v2391, v2393, v2396, v2399, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2341 s i := by
  change (v2585 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v2500, v2501, v2510, v2511, v2513, v2515, v2517, v2519, v2521, v2523, v2525, v2527, v2529, v2531, v2533, v2535, v2537, v2539, v2541, v2543, v2545, v2547, v2550, v2553, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2341 s i := by
  change (v2739 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v2654, v2655, v2664, v2665, v2667, v2669, v2671, v2673, v2675, v2677, v2679, v2681, v2683, v2685, v2687, v2689, v2691, v2693, v2695, v2697, v2699, v2701, v2704, v2707, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2341 s i := by
  change (v2893 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v2808, v2809, v2818, v2819, v2821, v2823, v2825, v2827, v2829, v2831, v2833, v2835, v2837, v2839, v2841, v2843, v2845, v2847, v2849, v2851, v2853, v2855, v2858, v2861, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2341 s i := by
  change (v3047 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v2962, v2963, v2972, v2973, v2975, v2977, v2979, v2981, v2983, v2985, v2987, v2989, v2991, v2993, v2995, v2997, v2999, v3001, v3003, v3005, v3007, v3009, v3012, v3015, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2341 s i := by
  change (v3201 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v3116, v3117, v3126, v3127, v3129, v3131, v3133, v3135, v3137, v3139, v3141, v3143, v3145, v3147, v3149, v3151, v3153, v3155, v3157, v3159, v3161, v3163, v3166, v3169, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2341 s i := by
  change (v3355 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v3270, v3271, v3280, v3281, v3283, v3285, v3287, v3289, v3291, v3293, v3295, v3297, v3299, v3301, v3303, v3305, v3307, v3309, v3311, v3313, v3315, v3317, v3320, v3323, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2341 s i := by
  change (v3509 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v3424, v3425, v3434, v3435, v3437, v3439, v3441, v3443, v3445, v3447, v3449, v3451, v3453, v3455, v3457, v3459, v3461, v3463, v3465, v3467, v3469, v3471, v3474, v3477, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2341 s i := by
  change (v3663 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v3578, v3579, v3588, v3589, v3591, v3593, v3595, v3597, v3599, v3601, v3603, v3605, v3607, v3609, v3611, v3613, v3615, v3617, v3619, v3621, v3623, v3625, v3628, v3631, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2341 s i := by
  change (v3817 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v3732, v3733, v3742, v3743, v3745, v3747, v3749, v3751, v3753, v3755, v3757, v3759, v3761, v3763, v3765, v3767, v3769, v3771, v3773, v3775, v3777, v3779, v3782, v3785, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2341 s i := by
  change (v3971 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v3886, v3887, v3896, v3897, v3899, v3901, v3903, v3905, v3907, v3909, v3911, v3913, v3915, v3917, v3919, v3921, v3923, v3925, v3927, v3929, v3931, v3933, v3936, v3939, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2341 s i := by
  change (v4125 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v4040, v4041, v4050, v4051, v4053, v4055, v4057, v4059, v4061, v4063, v4065, v4067, v4069, v4071, v4073, v4075, v4077, v4079, v4081, v4083, v4085, v4087, v4090, v4093, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2341 s i := by
  change (v4279 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v4194, v4195, v4204, v4205, v4207, v4209, v4211, v4213, v4215, v4217, v4219, v4221, v4223, v4225, v4227, v4229, v4231, v4233, v4235, v4237, v4239, v4241, v4244, v4247, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2341 s i := by
  change (v4433 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v4348, v4349, v4358, v4359, v4361, v4363, v4365, v4367, v4369, v4371, v4373, v4375, v4377, v4379, v4381, v4383, v4385, v4387, v4389, v4391, v4393, v4395, v4398, v4401, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2341 s i := by
  change (v4587 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v4502, v4503, v4512, v4513, v4515, v4517, v4519, v4521, v4523, v4525, v4527, v4529, v4531, v4533, v4535, v4537, v4539, v4541, v4543, v4545, v4547, v4549, v4552, v4555, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2341 s i := by
  change (v4705 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v4623, v4630, v4631, v4633, v4635, v4637, v4639, v4641, v4643, v4645, v4647, v4649, v4651, v4653, v4655, v4657, v4659, v4661, v4663, v4665, v4667, v4670, v4673, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2341 s i := by
  change (v4823 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v4741, v4748, v4749, v4751, v4753, v4755, v4757, v4759, v4761, v4763, v4765, v4767, v4769, v4771, v4773, v4775, v4777, v4779, v4781, v4783, v4785, v4788, v4791, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2341 s i := by
  change (v4941 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v4859, v4866, v4867, v4869, v4871, v4873, v4875, v4877, v4879, v4881, v4883, v4885, v4887, v4889, v4891, v4893, v4895, v4897, v4899, v4901, v4903, v4906, v4909, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2341 s i := by
  change (v5059 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v4977, v4984, v4985, v4987, v4989, v4991, v4993, v4995, v4997, v4999, v5001, v5003, v5005, v5007, v5009, v5011, v5013, v5015, v5017, v5019, v5021, v5024, v5027, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2341 s i := by
  change (v5177 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v5095, v5102, v5103, v5105, v5107, v5109, v5111, v5113, v5115, v5117, v5119, v5121, v5123, v5125, v5127, v5129, v5131, v5133, v5135, v5137, v5139, v5142, v5145, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2341 s i := by
  change (v5295 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v5213, v5220, v5221, v5223, v5225, v5227, v5229, v5231, v5233, v5235, v5237, v5239, v5241, v5243, v5245, v5247, v5249, v5251, v5253, v5255, v5257, v5260, v5263, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2341 s i := by
  change (v5413 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v5331, v5338, v5339, v5341, v5343, v5345, v5347, v5349, v5351, v5353, v5355, v5357, v5359, v5361, v5363, v5365, v5367, v5369, v5371, v5373, v5375, v5378, v5381, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2341 s i := by
  change (v5531 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v5449, v5456, v5457, v5459, v5461, v5463, v5465, v5467, v5469, v5471, v5473, v5475, v5477, v5479, v5481, v5483, v5485, v5487, v5489, v5491, v5493, v5496, v5499, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2341 s i := by
  change (v5649 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v5567, v5574, v5575, v5577, v5579, v5581, v5583, v5585, v5587, v5589, v5591, v5593, v5595, v5597, v5599, v5601, v5603, v5605, v5607, v5609, v5611, v5614, v5617, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2341 s i := by
  change (v5767 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v5685, v5692, v5693, v5695, v5697, v5699, v5701, v5703, v5705, v5707, v5709, v5711, v5713, v5715, v5717, v5719, v5721, v5723, v5725, v5727, v5729, v5732, v5735, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2341 s i := by
  change (v5885 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v5803, v5810, v5811, v5813, v5815, v5817, v5819, v5821, v5823, v5825, v5827, v5829, v5831, v5833, v5835, v5837, v5839, v5841, v5843, v5845, v5847, v5850, v5853, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2341 s i := by
  change (v6003 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v5921, v5928, v5929, v5931, v5933, v5935, v5937, v5939, v5941, v5943, v5945, v5947, v5949, v5951, v5953, v5955, v5957, v5959, v5961, v5963, v5965, v5968, v5971, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2341 s i := by
  change (v6121 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v6039, v6046, v6047, v6049, v6051, v6053, v6055, v6057, v6059, v6061, v6063, v6065, v6067, v6069, v6071, v6073, v6075, v6077, v6079, v6081, v6083, v6086, v6089, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2341 s i := by
  change (v6239 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v6157, v6164, v6165, v6167, v6169, v6171, v6173, v6175, v6177, v6179, v6181, v6183, v6185, v6187, v6189, v6191, v6193, v6195, v6197, v6199, v6201, v6204, v6207, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2341 s i := by
  change (v6357 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v6275, v6282, v6283, v6285, v6287, v6289, v6291, v6293, v6295, v6297, v6299, v6301, v6303, v6305, v6307, v6309, v6311, v6313, v6315, v6317, v6319, v6322, v6325, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
private theorem reference_sltiu_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2341 s i := by
  change (v6475 s i) = v2341 s i
  simp [v0, v1, ref_sltiu_v1005 s i commit known, ref_sltiu_v1013 s i commit known, ref_sltiu_v1021 s i commit known, ref_sltiu_v1029 s i commit known, ref_sltiu_v1037 s i commit known, ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, ref_sltiu_v1106 s i commit known, ref_sltiu_v1114 s i commit known, ref_sltiu_v1122 s i commit known, ref_sltiu_v1130 s i commit known, ref_sltiu_v1138 s i commit known, ref_sltiu_v1146 s i commit known, ref_sltiu_v1154 s i commit known, ref_sltiu_v1162 s i commit known, ref_sltiu_v1170 s i commit known, ref_sltiu_v1178 s i commit known, ref_sltiu_v1186 s i commit known, ref_sltiu_v1194 s i commit known, ref_sltiu_v1203 s i commit known, ref_sltiu_v1209 s i commit known, ref_sltiu_v1214 s i commit known, ref_sltiu_v1221 s i commit known, ref_sltiu_v1228 s i commit known, ref_sltiu_v1236 s i commit known, ref_sltiu_v1244 s i commit known, ref_sltiu_v1252 s i commit known, ref_sltiu_v1260 s i commit known, v6393, v6400, v6401, v6403, v6405, v6407, v6409, v6411, v6413, v6415, v6417, v6419, v6421, v6423, v6425, v6427, v6429, v6431, v6433, v6435, v6437, v6440, v6443, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_sltiu_v980 s i commit known, ref_sltiu_v989 s i commit known, ref_sltiu_v997 s i commit known, reset, target]
theorem reference_sltiu_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2341 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x1 s i reset commit known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x2 s i reset commit known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x3 s i reset commit known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x4 s i reset commit known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x5 s i reset commit known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x6 s i reset commit known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x7 s i reset commit known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x8 s i reset commit known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x9 s i reset commit known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x10 s i reset commit known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x11 s i reset commit known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x12 s i reset commit known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x13 s i reset commit known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x14 s i reset commit known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x15 s i reset commit known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x16 s i reset commit known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x17 s i reset commit known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x18 s i reset commit known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x19 s i reset commit known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x20 s i reset commit known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x21 s i reset commit known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x22 s i reset commit known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x23 s i reset commit known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x24 s i reset commit known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x25 s i reset commit known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x26 s i reset commit known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x27 s i reset commit known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x28 s i reset commit known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x29 s i reset commit known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x30 s i reset commit known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_sltiu_rd s i commit known).trans target
    rw [target]
    exact reference_sltiu_next_x31 s i reset commit known refTarget
#print axioms reference_sltiu_written_value
private theorem ref_xori_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_xori_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_xori_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1122 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1122 s i = 0 := by
  change (if (1073762355 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1130 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1130 s i = 0 := by
  change (if (1073741875 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1138 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1138 s i = 0 := by
  change (if (20531 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1146 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1146 s i = 0 := by
  change (if (4147 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1154 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1154 s i = 0 := by
  change (if (16435 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1162 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1162 s i = 0 := by
  change (if (24627 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 4261441663 24627 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1170 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1170 s i = 0 := by
  change (if (28723 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 4261441663 28723 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1178 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1178 s i = 0 := by
  change (if (12339 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1186 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1186 s i = 0 := by
  change (if (8243 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1194 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1194 s i = 0 := by
  change (if (51 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1203 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1203 s i = 0 := by
  change (if (23 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1209 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1209 s i = 0 := by
  change (if (55 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1214 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1214 s i = 0 := by
  change (if (1073762323 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1221 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1221 s i = 0 := by
  change (if (20499 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1228 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1228 s i = 0 := by
  change (if (4115 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1236 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1236 s i = 1 := by
  change (if (16403 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_xori_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_xori_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16403 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_xori_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1046 s i commit known, ref_xori_v1052 s i commit known, ref_xori_v1058 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v1237, ref_xori_v1333 s i commit known, ref_xori_v1339 s i commit known, ref_xori_v1345 s i commit known, ref_xori_v1351 s i commit known, ref_xori_v1358 s i commit known, ref_xori_v1365 s i commit known, ref_xori_v1372 s i commit known, ref_xori_v1379 s i commit known, ref_xori_v1386 s i commit known, v1589, v1600, v1601, v1602, v1603, v1604, v1605, v1606, v1607, v1608, v1609, v1610, v1611, v1612, v1613, v1614, v1615, v1616, v1617, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_xori_rd (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) :
    v1320 s i = BitVec.extractLsb' 7 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1046 s i commit known, ref_xori_v1052 s i commit known, ref_xori_v1058 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v1237, v1238, v1239, v1240, v1286, v1287, v1288, v1289, v1290, v1291, v1292, v1293, v1294, v1295, v1296, v1297, v1298, v1299, v1300, v1301, v1302, v1303, v1304, v1305, v1306, v1307, v1308, v1309, v1310, v1311, v1312, v1313, v1314, v1315, v1316, v1317, v1318, v1319, v1320, commit, reference_commit_instruction s i commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega, show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 25 by omega, show 7+j < 31 by omega, show 7+j < 32 by omega]
theorem reference_xori_immediate (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) : v2092 s i = immediateI s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_xori_v1046 s i commit known, ref_xori_v1052 s i commit known, ref_xori_v1058 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, ref_xori_v1333 s i commit known, ref_xori_v1339 s i commit known, ref_xori_v1345 s i commit known, ref_xori_v1351 s i commit known, ref_xori_v1358 s i commit known, ref_xori_v1365 s i commit known, ref_xori_v1372 s i commit known, ref_xori_v1379 s i commit known, ref_xori_v1386 s i commit known, v1804, v1816, v1817, v1818, v1819, v1820, v1821, v1822, v1823, v1824, v1825, v1826, v1827, v1828, v1829, v1831, v1832, v2044, v2045, v2046, v2067, v2068, v2069, v2070, v2071, v2072, v2073, v2074, v2075, v2076, v2077, v2078, v2079, v2080, v2081, v2082, v2083, v2084, v2085, v2086, v2087, v2088, v2089, v2090, v2091, v2092, commit, reference_commit_instruction s i commit, BitVec.reduceEq, if_true, if_false]
  rw [reference_sign_extension]
  rfl
theorem reference_xori_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_xori_rs1 s i commit known]
theorem aligned_reference_arithmetic_xori (s : State) (i : Inputs)
    (aligned : DecodedAluAligned s) (agree : RegisterAgreement s)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2331 s i := by
  have arithmetic := decoded_reference_immediate_xori s i s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
    s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc (referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst)) known
    (reference_xori_immediate s i commit known)
  rw [reference_xori_operand1 s i zero commit known] at arithmetic
  exact (decoded_alu_reference_operands s aligned agree).trans arithmetic
#print axioms aligned_reference_arithmetic_xori
private theorem reference_xori_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2331 s i := by
  change (v2431 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v2329, v2330, v2362, v2363, v2365, v2367, v2369, v2371, v2373, v2375, v2377, v2379, v2381, v2383, v2385, v2387, v2389, v2391, v2393, v2396, v2399, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2331 s i := by
  change (v2585 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v2494, v2495, v2516, v2517, v2519, v2521, v2523, v2525, v2527, v2529, v2531, v2533, v2535, v2537, v2539, v2541, v2543, v2545, v2547, v2550, v2553, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2331 s i := by
  change (v2739 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v2648, v2649, v2670, v2671, v2673, v2675, v2677, v2679, v2681, v2683, v2685, v2687, v2689, v2691, v2693, v2695, v2697, v2699, v2701, v2704, v2707, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2331 s i := by
  change (v2893 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v2802, v2803, v2824, v2825, v2827, v2829, v2831, v2833, v2835, v2837, v2839, v2841, v2843, v2845, v2847, v2849, v2851, v2853, v2855, v2858, v2861, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2331 s i := by
  change (v3047 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v2956, v2957, v2978, v2979, v2981, v2983, v2985, v2987, v2989, v2991, v2993, v2995, v2997, v2999, v3001, v3003, v3005, v3007, v3009, v3012, v3015, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2331 s i := by
  change (v3201 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v3110, v3111, v3132, v3133, v3135, v3137, v3139, v3141, v3143, v3145, v3147, v3149, v3151, v3153, v3155, v3157, v3159, v3161, v3163, v3166, v3169, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2331 s i := by
  change (v3355 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v3264, v3265, v3286, v3287, v3289, v3291, v3293, v3295, v3297, v3299, v3301, v3303, v3305, v3307, v3309, v3311, v3313, v3315, v3317, v3320, v3323, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2331 s i := by
  change (v3509 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v3418, v3419, v3440, v3441, v3443, v3445, v3447, v3449, v3451, v3453, v3455, v3457, v3459, v3461, v3463, v3465, v3467, v3469, v3471, v3474, v3477, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2331 s i := by
  change (v3663 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v3572, v3573, v3594, v3595, v3597, v3599, v3601, v3603, v3605, v3607, v3609, v3611, v3613, v3615, v3617, v3619, v3621, v3623, v3625, v3628, v3631, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2331 s i := by
  change (v3817 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v3726, v3727, v3748, v3749, v3751, v3753, v3755, v3757, v3759, v3761, v3763, v3765, v3767, v3769, v3771, v3773, v3775, v3777, v3779, v3782, v3785, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2331 s i := by
  change (v3971 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v3880, v3881, v3902, v3903, v3905, v3907, v3909, v3911, v3913, v3915, v3917, v3919, v3921, v3923, v3925, v3927, v3929, v3931, v3933, v3936, v3939, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2331 s i := by
  change (v4125 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v4034, v4035, v4056, v4057, v4059, v4061, v4063, v4065, v4067, v4069, v4071, v4073, v4075, v4077, v4079, v4081, v4083, v4085, v4087, v4090, v4093, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2331 s i := by
  change (v4279 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v4188, v4189, v4210, v4211, v4213, v4215, v4217, v4219, v4221, v4223, v4225, v4227, v4229, v4231, v4233, v4235, v4237, v4239, v4241, v4244, v4247, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2331 s i := by
  change (v4433 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v4342, v4343, v4364, v4365, v4367, v4369, v4371, v4373, v4375, v4377, v4379, v4381, v4383, v4385, v4387, v4389, v4391, v4393, v4395, v4398, v4401, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2331 s i := by
  change (v4587 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v4496, v4497, v4518, v4519, v4521, v4523, v4525, v4527, v4529, v4531, v4533, v4535, v4537, v4539, v4541, v4543, v4545, v4547, v4549, v4552, v4555, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2331 s i := by
  change (v4705 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v4620, v4636, v4637, v4639, v4641, v4643, v4645, v4647, v4649, v4651, v4653, v4655, v4657, v4659, v4661, v4663, v4665, v4667, v4670, v4673, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2331 s i := by
  change (v4823 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v4738, v4754, v4755, v4757, v4759, v4761, v4763, v4765, v4767, v4769, v4771, v4773, v4775, v4777, v4779, v4781, v4783, v4785, v4788, v4791, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2331 s i := by
  change (v4941 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v4856, v4872, v4873, v4875, v4877, v4879, v4881, v4883, v4885, v4887, v4889, v4891, v4893, v4895, v4897, v4899, v4901, v4903, v4906, v4909, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2331 s i := by
  change (v5059 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v4974, v4990, v4991, v4993, v4995, v4997, v4999, v5001, v5003, v5005, v5007, v5009, v5011, v5013, v5015, v5017, v5019, v5021, v5024, v5027, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2331 s i := by
  change (v5177 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v5092, v5108, v5109, v5111, v5113, v5115, v5117, v5119, v5121, v5123, v5125, v5127, v5129, v5131, v5133, v5135, v5137, v5139, v5142, v5145, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2331 s i := by
  change (v5295 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v5210, v5226, v5227, v5229, v5231, v5233, v5235, v5237, v5239, v5241, v5243, v5245, v5247, v5249, v5251, v5253, v5255, v5257, v5260, v5263, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2331 s i := by
  change (v5413 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v5328, v5344, v5345, v5347, v5349, v5351, v5353, v5355, v5357, v5359, v5361, v5363, v5365, v5367, v5369, v5371, v5373, v5375, v5378, v5381, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2331 s i := by
  change (v5531 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v5446, v5462, v5463, v5465, v5467, v5469, v5471, v5473, v5475, v5477, v5479, v5481, v5483, v5485, v5487, v5489, v5491, v5493, v5496, v5499, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2331 s i := by
  change (v5649 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v5564, v5580, v5581, v5583, v5585, v5587, v5589, v5591, v5593, v5595, v5597, v5599, v5601, v5603, v5605, v5607, v5609, v5611, v5614, v5617, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2331 s i := by
  change (v5767 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v5682, v5698, v5699, v5701, v5703, v5705, v5707, v5709, v5711, v5713, v5715, v5717, v5719, v5721, v5723, v5725, v5727, v5729, v5732, v5735, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2331 s i := by
  change (v5885 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v5800, v5816, v5817, v5819, v5821, v5823, v5825, v5827, v5829, v5831, v5833, v5835, v5837, v5839, v5841, v5843, v5845, v5847, v5850, v5853, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2331 s i := by
  change (v6003 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v5918, v5934, v5935, v5937, v5939, v5941, v5943, v5945, v5947, v5949, v5951, v5953, v5955, v5957, v5959, v5961, v5963, v5965, v5968, v5971, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2331 s i := by
  change (v6121 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v6036, v6052, v6053, v6055, v6057, v6059, v6061, v6063, v6065, v6067, v6069, v6071, v6073, v6075, v6077, v6079, v6081, v6083, v6086, v6089, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2331 s i := by
  change (v6239 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v6154, v6170, v6171, v6173, v6175, v6177, v6179, v6181, v6183, v6185, v6187, v6189, v6191, v6193, v6195, v6197, v6199, v6201, v6204, v6207, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2331 s i := by
  change (v6357 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v6272, v6288, v6289, v6291, v6293, v6295, v6297, v6299, v6301, v6303, v6305, v6307, v6309, v6311, v6313, v6315, v6317, v6319, v6322, v6325, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
private theorem reference_xori_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2331 s i := by
  change (v6475 s i) = v2331 s i
  simp [v0, v1, ref_xori_v1005 s i commit known, ref_xori_v1013 s i commit known, ref_xori_v1021 s i commit known, ref_xori_v1029 s i commit known, ref_xori_v1037 s i commit known, ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, ref_xori_v1106 s i commit known, ref_xori_v1114 s i commit known, ref_xori_v1122 s i commit known, ref_xori_v1130 s i commit known, ref_xori_v1138 s i commit known, ref_xori_v1146 s i commit known, ref_xori_v1154 s i commit known, ref_xori_v1162 s i commit known, ref_xori_v1170 s i commit known, ref_xori_v1178 s i commit known, ref_xori_v1186 s i commit known, ref_xori_v1194 s i commit known, ref_xori_v1203 s i commit known, ref_xori_v1209 s i commit known, ref_xori_v1214 s i commit known, ref_xori_v1221 s i commit known, ref_xori_v1228 s i commit known, ref_xori_v1236 s i commit known, v6390, v6406, v6407, v6409, v6411, v6413, v6415, v6417, v6419, v6421, v6423, v6425, v6427, v6429, v6431, v6433, v6435, v6437, v6440, v6443, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_xori_v980 s i commit known, ref_xori_v989 s i commit known, ref_xori_v997 s i commit known, reset, target]
theorem reference_xori_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2331 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x1 s i reset commit known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x2 s i reset commit known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x3 s i reset commit known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x4 s i reset commit known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x5 s i reset commit known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x6 s i reset commit known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x7 s i reset commit known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x8 s i reset commit known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x9 s i reset commit known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x10 s i reset commit known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x11 s i reset commit known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x12 s i reset commit known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x13 s i reset commit known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x14 s i reset commit known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x15 s i reset commit known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x16 s i reset commit known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x17 s i reset commit known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x18 s i reset commit known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x19 s i reset commit known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x20 s i reset commit known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x21 s i reset commit known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x22 s i reset commit known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x23 s i reset commit known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x24 s i reset commit known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x25 s i reset commit known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x26 s i reset commit known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x27 s i reset commit known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x28 s i reset commit known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x29 s i reset commit known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x30 s i reset commit known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_xori_rd s i commit known).trans target
    rw [target]
    exact reference_xori_next_x31 s i reset commit known refTarget
#print axioms reference_xori_written_value
private theorem ref_ori_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_ori_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_ori_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1122 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1122 s i = 0 := by
  change (if (1073762355 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1130 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1130 s i = 0 := by
  change (if (1073741875 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1138 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1138 s i = 0 := by
  change (if (20531 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1146 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1146 s i = 0 := by
  change (if (4147 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1154 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1154 s i = 0 := by
  change (if (16435 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1162 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1162 s i = 0 := by
  change (if (24627 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 4261441663 24627 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1170 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1170 s i = 0 := by
  change (if (28723 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 4261441663 28723 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1178 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1178 s i = 0 := by
  change (if (12339 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1186 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1186 s i = 0 := by
  change (if (8243 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1194 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1194 s i = 0 := by
  change (if (51 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1203 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1203 s i = 0 := by
  change (if (23 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1209 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1209 s i = 0 := by
  change (if (55 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1214 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1214 s i = 0 := by
  change (if (1073762323 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1221 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1221 s i = 0 := by
  change (if (20499 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1228 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1228 s i = 0 := by
  change (if (4115 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1236 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1236 s i = 0 := by
  change (if (16403 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1244 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1244 s i = 1 := by
  change (if (24595 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_ori_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_ori_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24595 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_ori_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1046 s i commit known, ref_ori_v1052 s i commit known, ref_ori_v1058 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v1245, ref_ori_v1333 s i commit known, ref_ori_v1339 s i commit known, ref_ori_v1345 s i commit known, ref_ori_v1351 s i commit known, ref_ori_v1358 s i commit known, ref_ori_v1365 s i commit known, ref_ori_v1372 s i commit known, ref_ori_v1379 s i commit known, ref_ori_v1386 s i commit known, v1590, v1599, v1600, v1601, v1602, v1603, v1604, v1605, v1606, v1607, v1608, v1609, v1610, v1611, v1612, v1613, v1614, v1615, v1616, v1617, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_ori_rd (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) :
    v1320 s i = BitVec.extractLsb' 7 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1046 s i commit known, ref_ori_v1052 s i commit known, ref_ori_v1058 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v1245, v1246, v1247, v1248, v1285, v1286, v1287, v1288, v1289, v1290, v1291, v1292, v1293, v1294, v1295, v1296, v1297, v1298, v1299, v1300, v1301, v1302, v1303, v1304, v1305, v1306, v1307, v1308, v1309, v1310, v1311, v1312, v1313, v1314, v1315, v1316, v1317, v1318, v1319, v1320, commit, reference_commit_instruction s i commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega, show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 25 by omega, show 7+j < 31 by omega, show 7+j < 32 by omega]
theorem reference_ori_immediate (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) : v2092 s i = immediateI s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_ori_v1046 s i commit known, ref_ori_v1052 s i commit known, ref_ori_v1058 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, ref_ori_v1333 s i commit known, ref_ori_v1339 s i commit known, ref_ori_v1345 s i commit known, ref_ori_v1351 s i commit known, ref_ori_v1358 s i commit known, ref_ori_v1365 s i commit known, ref_ori_v1372 s i commit known, ref_ori_v1379 s i commit known, ref_ori_v1386 s i commit known, v1805, v1815, v1816, v1817, v1818, v1819, v1820, v1821, v1822, v1823, v1824, v1825, v1826, v1827, v1828, v1829, v1831, v1832, v2047, v2048, v2049, v2066, v2067, v2068, v2069, v2070, v2071, v2072, v2073, v2074, v2075, v2076, v2077, v2078, v2079, v2080, v2081, v2082, v2083, v2084, v2085, v2086, v2087, v2088, v2089, v2090, v2091, v2092, commit, reference_commit_instruction s i commit, BitVec.reduceEq, if_true, if_false]
  rw [reference_sign_extension]
  rfl
theorem reference_ori_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_ori_rs1 s i commit known]
theorem aligned_reference_arithmetic_ori (s : State) (i : Inputs)
    (aligned : DecodedAluAligned s) (agree : RegisterAgreement s)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2334 s i := by
  have arithmetic := decoded_reference_immediate_ori s i s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
    s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc (referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst)) known
    (reference_ori_immediate s i commit known)
  rw [reference_ori_operand1 s i zero commit known] at arithmetic
  exact (decoded_alu_reference_operands s aligned agree).trans arithmetic
#print axioms aligned_reference_arithmetic_ori
private theorem reference_ori_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2334 s i := by
  change (v2431 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v2332, v2333, v2360, v2361, v2363, v2365, v2367, v2369, v2371, v2373, v2375, v2377, v2379, v2381, v2383, v2385, v2387, v2389, v2391, v2393, v2396, v2399, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2334 s i := by
  change (v2585 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v2496, v2497, v2514, v2515, v2517, v2519, v2521, v2523, v2525, v2527, v2529, v2531, v2533, v2535, v2537, v2539, v2541, v2543, v2545, v2547, v2550, v2553, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2334 s i := by
  change (v2739 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v2650, v2651, v2668, v2669, v2671, v2673, v2675, v2677, v2679, v2681, v2683, v2685, v2687, v2689, v2691, v2693, v2695, v2697, v2699, v2701, v2704, v2707, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2334 s i := by
  change (v2893 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v2804, v2805, v2822, v2823, v2825, v2827, v2829, v2831, v2833, v2835, v2837, v2839, v2841, v2843, v2845, v2847, v2849, v2851, v2853, v2855, v2858, v2861, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2334 s i := by
  change (v3047 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v2958, v2959, v2976, v2977, v2979, v2981, v2983, v2985, v2987, v2989, v2991, v2993, v2995, v2997, v2999, v3001, v3003, v3005, v3007, v3009, v3012, v3015, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2334 s i := by
  change (v3201 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v3112, v3113, v3130, v3131, v3133, v3135, v3137, v3139, v3141, v3143, v3145, v3147, v3149, v3151, v3153, v3155, v3157, v3159, v3161, v3163, v3166, v3169, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2334 s i := by
  change (v3355 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v3266, v3267, v3284, v3285, v3287, v3289, v3291, v3293, v3295, v3297, v3299, v3301, v3303, v3305, v3307, v3309, v3311, v3313, v3315, v3317, v3320, v3323, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2334 s i := by
  change (v3509 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v3420, v3421, v3438, v3439, v3441, v3443, v3445, v3447, v3449, v3451, v3453, v3455, v3457, v3459, v3461, v3463, v3465, v3467, v3469, v3471, v3474, v3477, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2334 s i := by
  change (v3663 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v3574, v3575, v3592, v3593, v3595, v3597, v3599, v3601, v3603, v3605, v3607, v3609, v3611, v3613, v3615, v3617, v3619, v3621, v3623, v3625, v3628, v3631, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2334 s i := by
  change (v3817 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v3728, v3729, v3746, v3747, v3749, v3751, v3753, v3755, v3757, v3759, v3761, v3763, v3765, v3767, v3769, v3771, v3773, v3775, v3777, v3779, v3782, v3785, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2334 s i := by
  change (v3971 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v3882, v3883, v3900, v3901, v3903, v3905, v3907, v3909, v3911, v3913, v3915, v3917, v3919, v3921, v3923, v3925, v3927, v3929, v3931, v3933, v3936, v3939, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2334 s i := by
  change (v4125 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v4036, v4037, v4054, v4055, v4057, v4059, v4061, v4063, v4065, v4067, v4069, v4071, v4073, v4075, v4077, v4079, v4081, v4083, v4085, v4087, v4090, v4093, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2334 s i := by
  change (v4279 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v4190, v4191, v4208, v4209, v4211, v4213, v4215, v4217, v4219, v4221, v4223, v4225, v4227, v4229, v4231, v4233, v4235, v4237, v4239, v4241, v4244, v4247, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2334 s i := by
  change (v4433 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v4344, v4345, v4362, v4363, v4365, v4367, v4369, v4371, v4373, v4375, v4377, v4379, v4381, v4383, v4385, v4387, v4389, v4391, v4393, v4395, v4398, v4401, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2334 s i := by
  change (v4587 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v4498, v4499, v4516, v4517, v4519, v4521, v4523, v4525, v4527, v4529, v4531, v4533, v4535, v4537, v4539, v4541, v4543, v4545, v4547, v4549, v4552, v4555, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2334 s i := by
  change (v4705 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v4621, v4634, v4635, v4637, v4639, v4641, v4643, v4645, v4647, v4649, v4651, v4653, v4655, v4657, v4659, v4661, v4663, v4665, v4667, v4670, v4673, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2334 s i := by
  change (v4823 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v4739, v4752, v4753, v4755, v4757, v4759, v4761, v4763, v4765, v4767, v4769, v4771, v4773, v4775, v4777, v4779, v4781, v4783, v4785, v4788, v4791, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2334 s i := by
  change (v4941 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v4857, v4870, v4871, v4873, v4875, v4877, v4879, v4881, v4883, v4885, v4887, v4889, v4891, v4893, v4895, v4897, v4899, v4901, v4903, v4906, v4909, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2334 s i := by
  change (v5059 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v4975, v4988, v4989, v4991, v4993, v4995, v4997, v4999, v5001, v5003, v5005, v5007, v5009, v5011, v5013, v5015, v5017, v5019, v5021, v5024, v5027, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2334 s i := by
  change (v5177 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v5093, v5106, v5107, v5109, v5111, v5113, v5115, v5117, v5119, v5121, v5123, v5125, v5127, v5129, v5131, v5133, v5135, v5137, v5139, v5142, v5145, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2334 s i := by
  change (v5295 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v5211, v5224, v5225, v5227, v5229, v5231, v5233, v5235, v5237, v5239, v5241, v5243, v5245, v5247, v5249, v5251, v5253, v5255, v5257, v5260, v5263, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2334 s i := by
  change (v5413 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v5329, v5342, v5343, v5345, v5347, v5349, v5351, v5353, v5355, v5357, v5359, v5361, v5363, v5365, v5367, v5369, v5371, v5373, v5375, v5378, v5381, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2334 s i := by
  change (v5531 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v5447, v5460, v5461, v5463, v5465, v5467, v5469, v5471, v5473, v5475, v5477, v5479, v5481, v5483, v5485, v5487, v5489, v5491, v5493, v5496, v5499, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2334 s i := by
  change (v5649 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v5565, v5578, v5579, v5581, v5583, v5585, v5587, v5589, v5591, v5593, v5595, v5597, v5599, v5601, v5603, v5605, v5607, v5609, v5611, v5614, v5617, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2334 s i := by
  change (v5767 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v5683, v5696, v5697, v5699, v5701, v5703, v5705, v5707, v5709, v5711, v5713, v5715, v5717, v5719, v5721, v5723, v5725, v5727, v5729, v5732, v5735, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2334 s i := by
  change (v5885 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v5801, v5814, v5815, v5817, v5819, v5821, v5823, v5825, v5827, v5829, v5831, v5833, v5835, v5837, v5839, v5841, v5843, v5845, v5847, v5850, v5853, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2334 s i := by
  change (v6003 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v5919, v5932, v5933, v5935, v5937, v5939, v5941, v5943, v5945, v5947, v5949, v5951, v5953, v5955, v5957, v5959, v5961, v5963, v5965, v5968, v5971, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2334 s i := by
  change (v6121 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v6037, v6050, v6051, v6053, v6055, v6057, v6059, v6061, v6063, v6065, v6067, v6069, v6071, v6073, v6075, v6077, v6079, v6081, v6083, v6086, v6089, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2334 s i := by
  change (v6239 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v6155, v6168, v6169, v6171, v6173, v6175, v6177, v6179, v6181, v6183, v6185, v6187, v6189, v6191, v6193, v6195, v6197, v6199, v6201, v6204, v6207, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2334 s i := by
  change (v6357 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v6273, v6286, v6287, v6289, v6291, v6293, v6295, v6297, v6299, v6301, v6303, v6305, v6307, v6309, v6311, v6313, v6315, v6317, v6319, v6322, v6325, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
private theorem reference_ori_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2334 s i := by
  change (v6475 s i) = v2334 s i
  simp [v0, v1, ref_ori_v1005 s i commit known, ref_ori_v1013 s i commit known, ref_ori_v1021 s i commit known, ref_ori_v1029 s i commit known, ref_ori_v1037 s i commit known, ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, ref_ori_v1106 s i commit known, ref_ori_v1114 s i commit known, ref_ori_v1122 s i commit known, ref_ori_v1130 s i commit known, ref_ori_v1138 s i commit known, ref_ori_v1146 s i commit known, ref_ori_v1154 s i commit known, ref_ori_v1162 s i commit known, ref_ori_v1170 s i commit known, ref_ori_v1178 s i commit known, ref_ori_v1186 s i commit known, ref_ori_v1194 s i commit known, ref_ori_v1203 s i commit known, ref_ori_v1209 s i commit known, ref_ori_v1214 s i commit known, ref_ori_v1221 s i commit known, ref_ori_v1228 s i commit known, ref_ori_v1236 s i commit known, ref_ori_v1244 s i commit known, v6391, v6404, v6405, v6407, v6409, v6411, v6413, v6415, v6417, v6419, v6421, v6423, v6425, v6427, v6429, v6431, v6433, v6435, v6437, v6440, v6443, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_ori_v980 s i commit known, ref_ori_v989 s i commit known, ref_ori_v997 s i commit known, reset, target]
theorem reference_ori_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2334 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x1 s i reset commit known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x2 s i reset commit known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x3 s i reset commit known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x4 s i reset commit known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x5 s i reset commit known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x6 s i reset commit known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x7 s i reset commit known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x8 s i reset commit known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x9 s i reset commit known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x10 s i reset commit known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x11 s i reset commit known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x12 s i reset commit known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x13 s i reset commit known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x14 s i reset commit known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x15 s i reset commit known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x16 s i reset commit known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x17 s i reset commit known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x18 s i reset commit known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x19 s i reset commit known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x20 s i reset commit known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x21 s i reset commit known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x22 s i reset commit known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x23 s i reset commit known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x24 s i reset commit known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x25 s i reset commit known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x26 s i reset commit known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x27 s i reset commit known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x28 s i reset commit known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x29 s i reset commit known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x30 s i reset commit known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_ori_rd s i commit known).trans target
    rw [target]
    exact reference_ori_next_x31 s i reset commit known refTarget
#print axioms reference_ori_written_value
private theorem ref_andi_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_andi_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_andi_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1122 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1122 s i = 0 := by
  change (if (1073762355 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1130 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1130 s i = 0 := by
  change (if (1073741875 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1138 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1138 s i = 0 := by
  change (if (20531 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1146 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1146 s i = 0 := by
  change (if (4147 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1154 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1154 s i = 0 := by
  change (if (16435 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1162 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1162 s i = 0 := by
  change (if (24627 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 4261441663 24627 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1170 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1170 s i = 0 := by
  change (if (28723 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 4261441663 28723 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1178 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1178 s i = 0 := by
  change (if (12339 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1186 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1186 s i = 0 := by
  change (if (8243 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1194 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1194 s i = 0 := by
  change (if (51 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1203 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1203 s i = 0 := by
  change (if (23 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1209 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1209 s i = 0 := by
  change (if (55 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1214 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1214 s i = 0 := by
  change (if (1073762323 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1221 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1221 s i = 0 := by
  change (if (20499 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1228 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1228 s i = 0 := by
  change (if (4115 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 4261441663 4115 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1236 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1236 s i = 0 := by
  change (if (16403 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 28799 16403 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1244 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1244 s i = 0 := by
  change (if (24595 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 28799 24595 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1252 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1252 s i = 1 := by
  change (if (28691 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_andi_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_andi_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28691 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_andi_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1046 s i commit known, ref_andi_v1052 s i commit known, ref_andi_v1058 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v1253, ref_andi_v1333 s i commit known, ref_andi_v1339 s i commit known, ref_andi_v1345 s i commit known, ref_andi_v1351 s i commit known, ref_andi_v1358 s i commit known, ref_andi_v1365 s i commit known, ref_andi_v1372 s i commit known, ref_andi_v1379 s i commit known, ref_andi_v1386 s i commit known, v1591, v1598, v1599, v1600, v1601, v1602, v1603, v1604, v1605, v1606, v1607, v1608, v1609, v1610, v1611, v1612, v1613, v1614, v1615, v1616, v1617, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_andi_rd (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) :
    v1320 s i = BitVec.extractLsb' 7 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1046 s i commit known, ref_andi_v1052 s i commit known, ref_andi_v1058 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v1253, v1254, v1255, v1256, v1284, v1285, v1286, v1287, v1288, v1289, v1290, v1291, v1292, v1293, v1294, v1295, v1296, v1297, v1298, v1299, v1300, v1301, v1302, v1303, v1304, v1305, v1306, v1307, v1308, v1309, v1310, v1311, v1312, v1313, v1314, v1315, v1316, v1317, v1318, v1319, v1320, commit, reference_commit_instruction s i commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega, show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 25 by omega, show 7+j < 31 by omega, show 7+j < 32 by omega]
theorem reference_andi_immediate (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) : v2092 s i = immediateI s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_andi_v1046 s i commit known, ref_andi_v1052 s i commit known, ref_andi_v1058 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, ref_andi_v1333 s i commit known, ref_andi_v1339 s i commit known, ref_andi_v1345 s i commit known, ref_andi_v1351 s i commit known, ref_andi_v1358 s i commit known, ref_andi_v1365 s i commit known, ref_andi_v1372 s i commit known, ref_andi_v1379 s i commit known, ref_andi_v1386 s i commit known, v1806, v1814, v1815, v1816, v1817, v1818, v1819, v1820, v1821, v1822, v1823, v1824, v1825, v1826, v1827, v1828, v1829, v1831, v1832, v2050, v2051, v2052, v2065, v2066, v2067, v2068, v2069, v2070, v2071, v2072, v2073, v2074, v2075, v2076, v2077, v2078, v2079, v2080, v2081, v2082, v2083, v2084, v2085, v2086, v2087, v2088, v2089, v2090, v2091, v2092, commit, reference_commit_instruction s i commit, BitVec.reduceEq, if_true, if_false]
  rw [reference_sign_extension]
  rfl
theorem reference_andi_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_andi_rs1 s i commit known]
theorem aligned_reference_arithmetic_andi (s : State) (i : Inputs)
    (aligned : DecodedAluAligned s) (agree : RegisterAgreement s)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2337 s i := by
  have arithmetic := decoded_reference_immediate_andi s i s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
    s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc (referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst)) known
    (reference_andi_immediate s i commit known)
  rw [reference_andi_operand1 s i zero commit known] at arithmetic
  exact (decoded_alu_reference_operands s aligned agree).trans arithmetic
#print axioms aligned_reference_arithmetic_andi
private theorem reference_andi_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2337 s i := by
  change (v2431 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v2335, v2336, v2358, v2359, v2361, v2363, v2365, v2367, v2369, v2371, v2373, v2375, v2377, v2379, v2381, v2383, v2385, v2387, v2389, v2391, v2393, v2396, v2399, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2337 s i := by
  change (v2585 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v2498, v2499, v2512, v2513, v2515, v2517, v2519, v2521, v2523, v2525, v2527, v2529, v2531, v2533, v2535, v2537, v2539, v2541, v2543, v2545, v2547, v2550, v2553, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2337 s i := by
  change (v2739 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v2652, v2653, v2666, v2667, v2669, v2671, v2673, v2675, v2677, v2679, v2681, v2683, v2685, v2687, v2689, v2691, v2693, v2695, v2697, v2699, v2701, v2704, v2707, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2337 s i := by
  change (v2893 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v2806, v2807, v2820, v2821, v2823, v2825, v2827, v2829, v2831, v2833, v2835, v2837, v2839, v2841, v2843, v2845, v2847, v2849, v2851, v2853, v2855, v2858, v2861, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2337 s i := by
  change (v3047 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v2960, v2961, v2974, v2975, v2977, v2979, v2981, v2983, v2985, v2987, v2989, v2991, v2993, v2995, v2997, v2999, v3001, v3003, v3005, v3007, v3009, v3012, v3015, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2337 s i := by
  change (v3201 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v3114, v3115, v3128, v3129, v3131, v3133, v3135, v3137, v3139, v3141, v3143, v3145, v3147, v3149, v3151, v3153, v3155, v3157, v3159, v3161, v3163, v3166, v3169, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2337 s i := by
  change (v3355 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v3268, v3269, v3282, v3283, v3285, v3287, v3289, v3291, v3293, v3295, v3297, v3299, v3301, v3303, v3305, v3307, v3309, v3311, v3313, v3315, v3317, v3320, v3323, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2337 s i := by
  change (v3509 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v3422, v3423, v3436, v3437, v3439, v3441, v3443, v3445, v3447, v3449, v3451, v3453, v3455, v3457, v3459, v3461, v3463, v3465, v3467, v3469, v3471, v3474, v3477, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2337 s i := by
  change (v3663 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v3576, v3577, v3590, v3591, v3593, v3595, v3597, v3599, v3601, v3603, v3605, v3607, v3609, v3611, v3613, v3615, v3617, v3619, v3621, v3623, v3625, v3628, v3631, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2337 s i := by
  change (v3817 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v3730, v3731, v3744, v3745, v3747, v3749, v3751, v3753, v3755, v3757, v3759, v3761, v3763, v3765, v3767, v3769, v3771, v3773, v3775, v3777, v3779, v3782, v3785, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2337 s i := by
  change (v3971 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v3884, v3885, v3898, v3899, v3901, v3903, v3905, v3907, v3909, v3911, v3913, v3915, v3917, v3919, v3921, v3923, v3925, v3927, v3929, v3931, v3933, v3936, v3939, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2337 s i := by
  change (v4125 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v4038, v4039, v4052, v4053, v4055, v4057, v4059, v4061, v4063, v4065, v4067, v4069, v4071, v4073, v4075, v4077, v4079, v4081, v4083, v4085, v4087, v4090, v4093, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2337 s i := by
  change (v4279 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v4192, v4193, v4206, v4207, v4209, v4211, v4213, v4215, v4217, v4219, v4221, v4223, v4225, v4227, v4229, v4231, v4233, v4235, v4237, v4239, v4241, v4244, v4247, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2337 s i := by
  change (v4433 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v4346, v4347, v4360, v4361, v4363, v4365, v4367, v4369, v4371, v4373, v4375, v4377, v4379, v4381, v4383, v4385, v4387, v4389, v4391, v4393, v4395, v4398, v4401, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2337 s i := by
  change (v4587 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v4500, v4501, v4514, v4515, v4517, v4519, v4521, v4523, v4525, v4527, v4529, v4531, v4533, v4535, v4537, v4539, v4541, v4543, v4545, v4547, v4549, v4552, v4555, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2337 s i := by
  change (v4705 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v4622, v4632, v4633, v4635, v4637, v4639, v4641, v4643, v4645, v4647, v4649, v4651, v4653, v4655, v4657, v4659, v4661, v4663, v4665, v4667, v4670, v4673, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2337 s i := by
  change (v4823 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v4740, v4750, v4751, v4753, v4755, v4757, v4759, v4761, v4763, v4765, v4767, v4769, v4771, v4773, v4775, v4777, v4779, v4781, v4783, v4785, v4788, v4791, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2337 s i := by
  change (v4941 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v4858, v4868, v4869, v4871, v4873, v4875, v4877, v4879, v4881, v4883, v4885, v4887, v4889, v4891, v4893, v4895, v4897, v4899, v4901, v4903, v4906, v4909, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2337 s i := by
  change (v5059 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v4976, v4986, v4987, v4989, v4991, v4993, v4995, v4997, v4999, v5001, v5003, v5005, v5007, v5009, v5011, v5013, v5015, v5017, v5019, v5021, v5024, v5027, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2337 s i := by
  change (v5177 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v5094, v5104, v5105, v5107, v5109, v5111, v5113, v5115, v5117, v5119, v5121, v5123, v5125, v5127, v5129, v5131, v5133, v5135, v5137, v5139, v5142, v5145, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2337 s i := by
  change (v5295 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v5212, v5222, v5223, v5225, v5227, v5229, v5231, v5233, v5235, v5237, v5239, v5241, v5243, v5245, v5247, v5249, v5251, v5253, v5255, v5257, v5260, v5263, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2337 s i := by
  change (v5413 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v5330, v5340, v5341, v5343, v5345, v5347, v5349, v5351, v5353, v5355, v5357, v5359, v5361, v5363, v5365, v5367, v5369, v5371, v5373, v5375, v5378, v5381, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2337 s i := by
  change (v5531 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v5448, v5458, v5459, v5461, v5463, v5465, v5467, v5469, v5471, v5473, v5475, v5477, v5479, v5481, v5483, v5485, v5487, v5489, v5491, v5493, v5496, v5499, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2337 s i := by
  change (v5649 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v5566, v5576, v5577, v5579, v5581, v5583, v5585, v5587, v5589, v5591, v5593, v5595, v5597, v5599, v5601, v5603, v5605, v5607, v5609, v5611, v5614, v5617, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2337 s i := by
  change (v5767 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v5684, v5694, v5695, v5697, v5699, v5701, v5703, v5705, v5707, v5709, v5711, v5713, v5715, v5717, v5719, v5721, v5723, v5725, v5727, v5729, v5732, v5735, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2337 s i := by
  change (v5885 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v5802, v5812, v5813, v5815, v5817, v5819, v5821, v5823, v5825, v5827, v5829, v5831, v5833, v5835, v5837, v5839, v5841, v5843, v5845, v5847, v5850, v5853, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2337 s i := by
  change (v6003 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v5920, v5930, v5931, v5933, v5935, v5937, v5939, v5941, v5943, v5945, v5947, v5949, v5951, v5953, v5955, v5957, v5959, v5961, v5963, v5965, v5968, v5971, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2337 s i := by
  change (v6121 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v6038, v6048, v6049, v6051, v6053, v6055, v6057, v6059, v6061, v6063, v6065, v6067, v6069, v6071, v6073, v6075, v6077, v6079, v6081, v6083, v6086, v6089, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2337 s i := by
  change (v6239 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v6156, v6166, v6167, v6169, v6171, v6173, v6175, v6177, v6179, v6181, v6183, v6185, v6187, v6189, v6191, v6193, v6195, v6197, v6199, v6201, v6204, v6207, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2337 s i := by
  change (v6357 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v6274, v6284, v6285, v6287, v6289, v6291, v6293, v6295, v6297, v6299, v6301, v6303, v6305, v6307, v6309, v6311, v6313, v6315, v6317, v6319, v6322, v6325, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
private theorem reference_andi_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2337 s i := by
  change (v6475 s i) = v2337 s i
  simp [v0, v1, ref_andi_v1005 s i commit known, ref_andi_v1013 s i commit known, ref_andi_v1021 s i commit known, ref_andi_v1029 s i commit known, ref_andi_v1037 s i commit known, ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, ref_andi_v1106 s i commit known, ref_andi_v1114 s i commit known, ref_andi_v1122 s i commit known, ref_andi_v1130 s i commit known, ref_andi_v1138 s i commit known, ref_andi_v1146 s i commit known, ref_andi_v1154 s i commit known, ref_andi_v1162 s i commit known, ref_andi_v1170 s i commit known, ref_andi_v1178 s i commit known, ref_andi_v1186 s i commit known, ref_andi_v1194 s i commit known, ref_andi_v1203 s i commit known, ref_andi_v1209 s i commit known, ref_andi_v1214 s i commit known, ref_andi_v1221 s i commit known, ref_andi_v1228 s i commit known, ref_andi_v1236 s i commit known, ref_andi_v1244 s i commit known, ref_andi_v1252 s i commit known, v6392, v6402, v6403, v6405, v6407, v6409, v6411, v6413, v6415, v6417, v6419, v6421, v6423, v6425, v6427, v6429, v6431, v6433, v6435, v6437, v6440, v6443, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_andi_v980 s i commit known, ref_andi_v989 s i commit known, ref_andi_v997 s i commit known, reset, target]
theorem reference_andi_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2337 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x1 s i reset commit known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x2 s i reset commit known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x3 s i reset commit known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x4 s i reset commit known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x5 s i reset commit known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x6 s i reset commit known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x7 s i reset commit known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x8 s i reset commit known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x9 s i reset commit known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x10 s i reset commit known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x11 s i reset commit known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x12 s i reset commit known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x13 s i reset commit known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x14 s i reset commit known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x15 s i reset commit known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x16 s i reset commit known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x17 s i reset commit known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x18 s i reset commit known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x19 s i reset commit known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x20 s i reset commit known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x21 s i reset commit known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x22 s i reset commit known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x23 s i reset commit known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x24 s i reset commit known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x25 s i reset commit known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x26 s i reset commit known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x27 s i reset commit known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x28 s i reset commit known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x29 s i reset commit known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x30 s i reset commit known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_andi_rd s i commit known).trans target
    rw [target]
    exact reference_andi_next_x31 s i reset commit known refTarget
#print axioms reference_andi_written_value
private theorem ref_slli_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_slli_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_slli_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1122 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1122 s i = 0 := by
  change (if (1073762355 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1130 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1130 s i = 0 := by
  change (if (1073741875 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1138 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1138 s i = 0 := by
  change (if (20531 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1146 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1146 s i = 0 := by
  change (if (4147 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1154 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1154 s i = 0 := by
  change (if (16435 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1162 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1162 s i = 0 := by
  change (if (24627 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 4261441663 24627 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1170 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1170 s i = 0 := by
  change (if (28723 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 4261441663 28723 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1178 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1178 s i = 0 := by
  change (if (12339 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1186 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1186 s i = 0 := by
  change (if (8243 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1194 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1194 s i = 0 := by
  change (if (51 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1203 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1203 s i = 0 := by
  change (if (23 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1209 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1209 s i = 0 := by
  change (if (55 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1214 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1214 s i = 0 := by
  change (if (1073762323 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1221 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1221 s i = 0 := by
  change (if (20499 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 4261441663 20499 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1228 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1228 s i = 1 := by
  change (if (4115 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 4261441663 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_slli_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_slli_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 4115 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_slli_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1046 s i commit known, ref_slli_v1052 s i commit known, ref_slli_v1058 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v1229, ref_slli_v1333 s i commit known, ref_slli_v1339 s i commit known, ref_slli_v1345 s i commit known, ref_slli_v1351 s i commit known, ref_slli_v1358 s i commit known, ref_slli_v1365 s i commit known, ref_slli_v1372 s i commit known, ref_slli_v1379 s i commit known, ref_slli_v1386 s i commit known, v1588, v1601, v1602, v1603, v1604, v1605, v1606, v1607, v1608, v1609, v1610, v1611, v1612, v1613, v1614, v1615, v1616, v1617, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_slli_rd (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) :
    v1320 s i = BitVec.extractLsb' 7 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1046 s i commit known, ref_slli_v1052 s i commit known, ref_slli_v1058 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v1229, v1230, v1231, v1232, v1287, v1288, v1289, v1290, v1291, v1292, v1293, v1294, v1295, v1296, v1297, v1298, v1299, v1300, v1301, v1302, v1303, v1304, v1305, v1306, v1307, v1308, v1309, v1310, v1311, v1312, v1313, v1314, v1315, v1316, v1317, v1318, v1319, v1320, commit, reference_commit_instruction s i commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega, show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 25 by omega, show 7+j < 31 by omega, show 7+j < 32 by omega]
theorem reference_slli_immediate (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) : v2092 s i = immediateI s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_slli_v1046 s i commit known, ref_slli_v1052 s i commit known, ref_slli_v1058 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, ref_slli_v1333 s i commit known, ref_slli_v1339 s i commit known, ref_slli_v1345 s i commit known, ref_slli_v1351 s i commit known, ref_slli_v1358 s i commit known, ref_slli_v1365 s i commit known, ref_slli_v1372 s i commit known, ref_slli_v1379 s i commit known, ref_slli_v1386 s i commit known, v1803, v1817, v1818, v1819, v1820, v1821, v1822, v1823, v1824, v1825, v1826, v1827, v1828, v1829, v1831, v1832, v2041, v2042, v2043, v2068, v2069, v2070, v2071, v2072, v2073, v2074, v2075, v2076, v2077, v2078, v2079, v2080, v2081, v2082, v2083, v2084, v2085, v2086, v2087, v2088, v2089, v2090, v2091, v2092, commit, reference_commit_instruction s i commit, BitVec.reduceEq, if_true, if_false]
  rw [reference_sign_extension]
  rfl
theorem reference_slli_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_slli_rs1 s i commit known]
theorem aligned_reference_arithmetic_slli (s : State) (i : Inputs)
    (aligned : DecodedAluAligned s) (agree : RegisterAgreement s)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2328 s i := by
  have arithmetic := decoded_reference_immediate_slli s i s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
    s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc (referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst)) known
    (reference_slli_immediate s i commit known)
  rw [reference_slli_operand1 s i zero commit known] at arithmetic
  exact (decoded_alu_reference_operands s aligned agree).trans arithmetic
#print axioms aligned_reference_arithmetic_slli
private theorem reference_slli_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2328 s i := by
  change (v2431 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v2322, v2323, v2364, v2365, v2367, v2369, v2371, v2373, v2375, v2377, v2379, v2381, v2383, v2385, v2387, v2389, v2391, v2393, v2396, v2399, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2328 s i := by
  change (v2585 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v2492, v2493, v2518, v2519, v2521, v2523, v2525, v2527, v2529, v2531, v2533, v2535, v2537, v2539, v2541, v2543, v2545, v2547, v2550, v2553, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2328 s i := by
  change (v2739 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v2646, v2647, v2672, v2673, v2675, v2677, v2679, v2681, v2683, v2685, v2687, v2689, v2691, v2693, v2695, v2697, v2699, v2701, v2704, v2707, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2328 s i := by
  change (v2893 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v2800, v2801, v2826, v2827, v2829, v2831, v2833, v2835, v2837, v2839, v2841, v2843, v2845, v2847, v2849, v2851, v2853, v2855, v2858, v2861, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2328 s i := by
  change (v3047 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v2954, v2955, v2980, v2981, v2983, v2985, v2987, v2989, v2991, v2993, v2995, v2997, v2999, v3001, v3003, v3005, v3007, v3009, v3012, v3015, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2328 s i := by
  change (v3201 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v3108, v3109, v3134, v3135, v3137, v3139, v3141, v3143, v3145, v3147, v3149, v3151, v3153, v3155, v3157, v3159, v3161, v3163, v3166, v3169, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2328 s i := by
  change (v3355 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v3262, v3263, v3288, v3289, v3291, v3293, v3295, v3297, v3299, v3301, v3303, v3305, v3307, v3309, v3311, v3313, v3315, v3317, v3320, v3323, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2328 s i := by
  change (v3509 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v3416, v3417, v3442, v3443, v3445, v3447, v3449, v3451, v3453, v3455, v3457, v3459, v3461, v3463, v3465, v3467, v3469, v3471, v3474, v3477, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2328 s i := by
  change (v3663 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v3570, v3571, v3596, v3597, v3599, v3601, v3603, v3605, v3607, v3609, v3611, v3613, v3615, v3617, v3619, v3621, v3623, v3625, v3628, v3631, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2328 s i := by
  change (v3817 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v3724, v3725, v3750, v3751, v3753, v3755, v3757, v3759, v3761, v3763, v3765, v3767, v3769, v3771, v3773, v3775, v3777, v3779, v3782, v3785, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2328 s i := by
  change (v3971 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v3878, v3879, v3904, v3905, v3907, v3909, v3911, v3913, v3915, v3917, v3919, v3921, v3923, v3925, v3927, v3929, v3931, v3933, v3936, v3939, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2328 s i := by
  change (v4125 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v4032, v4033, v4058, v4059, v4061, v4063, v4065, v4067, v4069, v4071, v4073, v4075, v4077, v4079, v4081, v4083, v4085, v4087, v4090, v4093, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2328 s i := by
  change (v4279 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v4186, v4187, v4212, v4213, v4215, v4217, v4219, v4221, v4223, v4225, v4227, v4229, v4231, v4233, v4235, v4237, v4239, v4241, v4244, v4247, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2328 s i := by
  change (v4433 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v4340, v4341, v4366, v4367, v4369, v4371, v4373, v4375, v4377, v4379, v4381, v4383, v4385, v4387, v4389, v4391, v4393, v4395, v4398, v4401, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2328 s i := by
  change (v4587 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v4494, v4495, v4520, v4521, v4523, v4525, v4527, v4529, v4531, v4533, v4535, v4537, v4539, v4541, v4543, v4545, v4547, v4549, v4552, v4555, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2328 s i := by
  change (v4705 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v4619, v4638, v4639, v4641, v4643, v4645, v4647, v4649, v4651, v4653, v4655, v4657, v4659, v4661, v4663, v4665, v4667, v4670, v4673, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2328 s i := by
  change (v4823 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v4737, v4756, v4757, v4759, v4761, v4763, v4765, v4767, v4769, v4771, v4773, v4775, v4777, v4779, v4781, v4783, v4785, v4788, v4791, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2328 s i := by
  change (v4941 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v4855, v4874, v4875, v4877, v4879, v4881, v4883, v4885, v4887, v4889, v4891, v4893, v4895, v4897, v4899, v4901, v4903, v4906, v4909, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2328 s i := by
  change (v5059 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v4973, v4992, v4993, v4995, v4997, v4999, v5001, v5003, v5005, v5007, v5009, v5011, v5013, v5015, v5017, v5019, v5021, v5024, v5027, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2328 s i := by
  change (v5177 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v5091, v5110, v5111, v5113, v5115, v5117, v5119, v5121, v5123, v5125, v5127, v5129, v5131, v5133, v5135, v5137, v5139, v5142, v5145, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2328 s i := by
  change (v5295 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v5209, v5228, v5229, v5231, v5233, v5235, v5237, v5239, v5241, v5243, v5245, v5247, v5249, v5251, v5253, v5255, v5257, v5260, v5263, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2328 s i := by
  change (v5413 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v5327, v5346, v5347, v5349, v5351, v5353, v5355, v5357, v5359, v5361, v5363, v5365, v5367, v5369, v5371, v5373, v5375, v5378, v5381, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2328 s i := by
  change (v5531 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v5445, v5464, v5465, v5467, v5469, v5471, v5473, v5475, v5477, v5479, v5481, v5483, v5485, v5487, v5489, v5491, v5493, v5496, v5499, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2328 s i := by
  change (v5649 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v5563, v5582, v5583, v5585, v5587, v5589, v5591, v5593, v5595, v5597, v5599, v5601, v5603, v5605, v5607, v5609, v5611, v5614, v5617, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2328 s i := by
  change (v5767 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v5681, v5700, v5701, v5703, v5705, v5707, v5709, v5711, v5713, v5715, v5717, v5719, v5721, v5723, v5725, v5727, v5729, v5732, v5735, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2328 s i := by
  change (v5885 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v5799, v5818, v5819, v5821, v5823, v5825, v5827, v5829, v5831, v5833, v5835, v5837, v5839, v5841, v5843, v5845, v5847, v5850, v5853, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2328 s i := by
  change (v6003 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v5917, v5936, v5937, v5939, v5941, v5943, v5945, v5947, v5949, v5951, v5953, v5955, v5957, v5959, v5961, v5963, v5965, v5968, v5971, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2328 s i := by
  change (v6121 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v6035, v6054, v6055, v6057, v6059, v6061, v6063, v6065, v6067, v6069, v6071, v6073, v6075, v6077, v6079, v6081, v6083, v6086, v6089, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2328 s i := by
  change (v6239 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v6153, v6172, v6173, v6175, v6177, v6179, v6181, v6183, v6185, v6187, v6189, v6191, v6193, v6195, v6197, v6199, v6201, v6204, v6207, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2328 s i := by
  change (v6357 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v6271, v6290, v6291, v6293, v6295, v6297, v6299, v6301, v6303, v6305, v6307, v6309, v6311, v6313, v6315, v6317, v6319, v6322, v6325, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
private theorem reference_slli_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2328 s i := by
  change (v6475 s i) = v2328 s i
  simp [v0, v1, ref_slli_v1005 s i commit known, ref_slli_v1013 s i commit known, ref_slli_v1021 s i commit known, ref_slli_v1029 s i commit known, ref_slli_v1037 s i commit known, ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, ref_slli_v1106 s i commit known, ref_slli_v1114 s i commit known, ref_slli_v1122 s i commit known, ref_slli_v1130 s i commit known, ref_slli_v1138 s i commit known, ref_slli_v1146 s i commit known, ref_slli_v1154 s i commit known, ref_slli_v1162 s i commit known, ref_slli_v1170 s i commit known, ref_slli_v1178 s i commit known, ref_slli_v1186 s i commit known, ref_slli_v1194 s i commit known, ref_slli_v1203 s i commit known, ref_slli_v1209 s i commit known, ref_slli_v1214 s i commit known, ref_slli_v1221 s i commit known, ref_slli_v1228 s i commit known, v6389, v6408, v6409, v6411, v6413, v6415, v6417, v6419, v6421, v6423, v6425, v6427, v6429, v6431, v6433, v6435, v6437, v6440, v6443, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_slli_v980 s i commit known, ref_slli_v989 s i commit known, ref_slli_v997 s i commit known, reset, target]
theorem reference_slli_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2328 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x1 s i reset commit known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x2 s i reset commit known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x3 s i reset commit known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x4 s i reset commit known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x5 s i reset commit known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x6 s i reset commit known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x7 s i reset commit known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x8 s i reset commit known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x9 s i reset commit known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x10 s i reset commit known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x11 s i reset commit known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x12 s i reset commit known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x13 s i reset commit known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x14 s i reset commit known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x15 s i reset commit known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x16 s i reset commit known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x17 s i reset commit known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x18 s i reset commit known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x19 s i reset commit known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x20 s i reset commit known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x21 s i reset commit known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x22 s i reset commit known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x23 s i reset commit known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x24 s i reset commit known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x25 s i reset commit known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x26 s i reset commit known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x27 s i reset commit known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x28 s i reset commit known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x29 s i reset commit known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x30 s i reset commit known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_slli_rd s i commit known).trans target
    rw [target]
    exact reference_slli_next_x31 s i reset commit known refTarget
#print axioms reference_slli_written_value
private theorem ref_srli_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_srli_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_srli_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1122 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1122 s i = 0 := by
  change (if (1073762355 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1130 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1130 s i = 0 := by
  change (if (1073741875 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1138 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1138 s i = 0 := by
  change (if (20531 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1146 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1146 s i = 0 := by
  change (if (4147 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1154 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1154 s i = 0 := by
  change (if (16435 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1162 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1162 s i = 0 := by
  change (if (24627 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 4261441663 24627 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1170 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1170 s i = 0 := by
  change (if (28723 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 4261441663 28723 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1178 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1178 s i = 0 := by
  change (if (12339 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1186 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1186 s i = 0 := by
  change (if (8243 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1194 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1194 s i = 0 := by
  change (if (51 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1203 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1203 s i = 0 := by
  change (if (23 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1209 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1209 s i = 0 := by
  change (if (55 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1214 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1214 s i = 0 := by
  change (if (1073762323 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 4261441663 1073762323 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1221 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1221 s i = 1 := by
  change (if (20499 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 4261441663 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_srli_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srli_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 20499 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_srli_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1046 s i commit known, ref_srli_v1052 s i commit known, ref_srli_v1058 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v1222, ref_srli_v1333 s i commit known, ref_srli_v1339 s i commit known, ref_srli_v1345 s i commit known, ref_srli_v1351 s i commit known, ref_srli_v1358 s i commit known, ref_srli_v1365 s i commit known, ref_srli_v1372 s i commit known, ref_srli_v1379 s i commit known, ref_srli_v1386 s i commit known, v1587, v1602, v1603, v1604, v1605, v1606, v1607, v1608, v1609, v1610, v1611, v1612, v1613, v1614, v1615, v1616, v1617, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_srli_rd (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) :
    v1320 s i = BitVec.extractLsb' 7 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1046 s i commit known, ref_srli_v1052 s i commit known, ref_srli_v1058 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v1222, v1223, v1224, v1225, v1288, v1289, v1290, v1291, v1292, v1293, v1294, v1295, v1296, v1297, v1298, v1299, v1300, v1301, v1302, v1303, v1304, v1305, v1306, v1307, v1308, v1309, v1310, v1311, v1312, v1313, v1314, v1315, v1316, v1317, v1318, v1319, v1320, commit, reference_commit_instruction s i commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega, show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 25 by omega, show 7+j < 31 by omega, show 7+j < 32 by omega]
theorem reference_srli_immediate (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) : v2092 s i = immediateI s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_srli_v1046 s i commit known, ref_srli_v1052 s i commit known, ref_srli_v1058 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, ref_srli_v1333 s i commit known, ref_srli_v1339 s i commit known, ref_srli_v1345 s i commit known, ref_srli_v1351 s i commit known, ref_srli_v1358 s i commit known, ref_srli_v1365 s i commit known, ref_srli_v1372 s i commit known, ref_srli_v1379 s i commit known, ref_srli_v1386 s i commit known, v1802, v1818, v1819, v1820, v1821, v1822, v1823, v1824, v1825, v1826, v1827, v1828, v1829, v1831, v1832, v2038, v2039, v2040, v2069, v2070, v2071, v2072, v2073, v2074, v2075, v2076, v2077, v2078, v2079, v2080, v2081, v2082, v2083, v2084, v2085, v2086, v2087, v2088, v2089, v2090, v2091, v2092, commit, reference_commit_instruction s i commit, BitVec.reduceEq, if_true, if_false]
  rw [reference_sign_extension]
  rfl
theorem reference_srli_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_srli_rs1 s i commit known]
theorem aligned_reference_arithmetic_srli (s : State) (i : Inputs)
    (aligned : DecodedAluAligned s) (agree : RegisterAgreement s)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2321 s i := by
  have arithmetic := decoded_reference_immediate_srli s i s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
    s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc (referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst)) known
    (reference_srli_immediate s i commit known)
  rw [reference_srli_operand1 s i zero commit known] at arithmetic
  exact (decoded_alu_reference_operands s aligned agree).trans arithmetic
#print axioms aligned_reference_arithmetic_srli
private theorem reference_srli_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2321 s i := by
  change (v2431 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v2317, v2318, v2366, v2367, v2369, v2371, v2373, v2375, v2377, v2379, v2381, v2383, v2385, v2387, v2389, v2391, v2393, v2396, v2399, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2321 s i := by
  change (v2585 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v2490, v2491, v2520, v2521, v2523, v2525, v2527, v2529, v2531, v2533, v2535, v2537, v2539, v2541, v2543, v2545, v2547, v2550, v2553, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2321 s i := by
  change (v2739 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v2644, v2645, v2674, v2675, v2677, v2679, v2681, v2683, v2685, v2687, v2689, v2691, v2693, v2695, v2697, v2699, v2701, v2704, v2707, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2321 s i := by
  change (v2893 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v2798, v2799, v2828, v2829, v2831, v2833, v2835, v2837, v2839, v2841, v2843, v2845, v2847, v2849, v2851, v2853, v2855, v2858, v2861, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2321 s i := by
  change (v3047 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v2952, v2953, v2982, v2983, v2985, v2987, v2989, v2991, v2993, v2995, v2997, v2999, v3001, v3003, v3005, v3007, v3009, v3012, v3015, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2321 s i := by
  change (v3201 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v3106, v3107, v3136, v3137, v3139, v3141, v3143, v3145, v3147, v3149, v3151, v3153, v3155, v3157, v3159, v3161, v3163, v3166, v3169, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2321 s i := by
  change (v3355 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v3260, v3261, v3290, v3291, v3293, v3295, v3297, v3299, v3301, v3303, v3305, v3307, v3309, v3311, v3313, v3315, v3317, v3320, v3323, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2321 s i := by
  change (v3509 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v3414, v3415, v3444, v3445, v3447, v3449, v3451, v3453, v3455, v3457, v3459, v3461, v3463, v3465, v3467, v3469, v3471, v3474, v3477, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2321 s i := by
  change (v3663 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v3568, v3569, v3598, v3599, v3601, v3603, v3605, v3607, v3609, v3611, v3613, v3615, v3617, v3619, v3621, v3623, v3625, v3628, v3631, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2321 s i := by
  change (v3817 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v3722, v3723, v3752, v3753, v3755, v3757, v3759, v3761, v3763, v3765, v3767, v3769, v3771, v3773, v3775, v3777, v3779, v3782, v3785, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2321 s i := by
  change (v3971 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v3876, v3877, v3906, v3907, v3909, v3911, v3913, v3915, v3917, v3919, v3921, v3923, v3925, v3927, v3929, v3931, v3933, v3936, v3939, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2321 s i := by
  change (v4125 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v4030, v4031, v4060, v4061, v4063, v4065, v4067, v4069, v4071, v4073, v4075, v4077, v4079, v4081, v4083, v4085, v4087, v4090, v4093, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2321 s i := by
  change (v4279 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v4184, v4185, v4214, v4215, v4217, v4219, v4221, v4223, v4225, v4227, v4229, v4231, v4233, v4235, v4237, v4239, v4241, v4244, v4247, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2321 s i := by
  change (v4433 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v4338, v4339, v4368, v4369, v4371, v4373, v4375, v4377, v4379, v4381, v4383, v4385, v4387, v4389, v4391, v4393, v4395, v4398, v4401, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2321 s i := by
  change (v4587 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v4492, v4493, v4522, v4523, v4525, v4527, v4529, v4531, v4533, v4535, v4537, v4539, v4541, v4543, v4545, v4547, v4549, v4552, v4555, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2321 s i := by
  change (v4705 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v4618, v4640, v4641, v4643, v4645, v4647, v4649, v4651, v4653, v4655, v4657, v4659, v4661, v4663, v4665, v4667, v4670, v4673, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2321 s i := by
  change (v4823 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v4736, v4758, v4759, v4761, v4763, v4765, v4767, v4769, v4771, v4773, v4775, v4777, v4779, v4781, v4783, v4785, v4788, v4791, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2321 s i := by
  change (v4941 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v4854, v4876, v4877, v4879, v4881, v4883, v4885, v4887, v4889, v4891, v4893, v4895, v4897, v4899, v4901, v4903, v4906, v4909, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2321 s i := by
  change (v5059 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v4972, v4994, v4995, v4997, v4999, v5001, v5003, v5005, v5007, v5009, v5011, v5013, v5015, v5017, v5019, v5021, v5024, v5027, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2321 s i := by
  change (v5177 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v5090, v5112, v5113, v5115, v5117, v5119, v5121, v5123, v5125, v5127, v5129, v5131, v5133, v5135, v5137, v5139, v5142, v5145, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2321 s i := by
  change (v5295 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v5208, v5230, v5231, v5233, v5235, v5237, v5239, v5241, v5243, v5245, v5247, v5249, v5251, v5253, v5255, v5257, v5260, v5263, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2321 s i := by
  change (v5413 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v5326, v5348, v5349, v5351, v5353, v5355, v5357, v5359, v5361, v5363, v5365, v5367, v5369, v5371, v5373, v5375, v5378, v5381, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2321 s i := by
  change (v5531 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v5444, v5466, v5467, v5469, v5471, v5473, v5475, v5477, v5479, v5481, v5483, v5485, v5487, v5489, v5491, v5493, v5496, v5499, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2321 s i := by
  change (v5649 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v5562, v5584, v5585, v5587, v5589, v5591, v5593, v5595, v5597, v5599, v5601, v5603, v5605, v5607, v5609, v5611, v5614, v5617, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2321 s i := by
  change (v5767 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v5680, v5702, v5703, v5705, v5707, v5709, v5711, v5713, v5715, v5717, v5719, v5721, v5723, v5725, v5727, v5729, v5732, v5735, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2321 s i := by
  change (v5885 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v5798, v5820, v5821, v5823, v5825, v5827, v5829, v5831, v5833, v5835, v5837, v5839, v5841, v5843, v5845, v5847, v5850, v5853, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2321 s i := by
  change (v6003 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v5916, v5938, v5939, v5941, v5943, v5945, v5947, v5949, v5951, v5953, v5955, v5957, v5959, v5961, v5963, v5965, v5968, v5971, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2321 s i := by
  change (v6121 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v6034, v6056, v6057, v6059, v6061, v6063, v6065, v6067, v6069, v6071, v6073, v6075, v6077, v6079, v6081, v6083, v6086, v6089, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2321 s i := by
  change (v6239 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v6152, v6174, v6175, v6177, v6179, v6181, v6183, v6185, v6187, v6189, v6191, v6193, v6195, v6197, v6199, v6201, v6204, v6207, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2321 s i := by
  change (v6357 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v6270, v6292, v6293, v6295, v6297, v6299, v6301, v6303, v6305, v6307, v6309, v6311, v6313, v6315, v6317, v6319, v6322, v6325, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
private theorem reference_srli_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2321 s i := by
  change (v6475 s i) = v2321 s i
  simp [v0, v1, ref_srli_v1005 s i commit known, ref_srli_v1013 s i commit known, ref_srli_v1021 s i commit known, ref_srli_v1029 s i commit known, ref_srli_v1037 s i commit known, ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, ref_srli_v1106 s i commit known, ref_srli_v1114 s i commit known, ref_srli_v1122 s i commit known, ref_srli_v1130 s i commit known, ref_srli_v1138 s i commit known, ref_srli_v1146 s i commit known, ref_srli_v1154 s i commit known, ref_srli_v1162 s i commit known, ref_srli_v1170 s i commit known, ref_srli_v1178 s i commit known, ref_srli_v1186 s i commit known, ref_srli_v1194 s i commit known, ref_srli_v1203 s i commit known, ref_srli_v1209 s i commit known, ref_srli_v1214 s i commit known, ref_srli_v1221 s i commit known, v6388, v6410, v6411, v6413, v6415, v6417, v6419, v6421, v6423, v6425, v6427, v6429, v6431, v6433, v6435, v6437, v6440, v6443, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_srli_v980 s i commit known, ref_srli_v989 s i commit known, ref_srli_v997 s i commit known, reset, target]
theorem reference_srli_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2321 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x1 s i reset commit known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x2 s i reset commit known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x3 s i reset commit known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x4 s i reset commit known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x5 s i reset commit known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x6 s i reset commit known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x7 s i reset commit known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x8 s i reset commit known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x9 s i reset commit known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x10 s i reset commit known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x11 s i reset commit known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x12 s i reset commit known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x13 s i reset commit known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x14 s i reset commit known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x15 s i reset commit known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x16 s i reset commit known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x17 s i reset commit known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x18 s i reset commit known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x19 s i reset commit known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x20 s i reset commit known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x21 s i reset commit known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x22 s i reset commit known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x23 s i reset commit known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x24 s i reset commit known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x25 s i reset commit known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x26 s i reset commit known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x27 s i reset commit known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x28 s i reset commit known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x29 s i reset commit known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x30 s i reset commit known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_srli_rd s i commit known).trans target
    rw [target]
    exact reference_srli_next_x31 s i reset commit known refTarget
#print axioms reference_srli_written_value
private theorem ref_srai_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_srai_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_srai_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1122 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1122 s i = 0 := by
  change (if (1073762355 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 4261441663 1073762355 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1130 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1130 s i = 0 := by
  change (if (1073741875 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 4261441663 1073741875 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1138 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1138 s i = 0 := by
  change (if (20531 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 4261441663 20531 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1146 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1146 s i = 0 := by
  change (if (4147 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 4261441663 4147 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1154 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1154 s i = 0 := by
  change (if (16435 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 4261441663 16435 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1162 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1162 s i = 0 := by
  change (if (24627 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 4261441663 24627 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1170 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1170 s i = 0 := by
  change (if (28723 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 4261441663 28723 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1178 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1178 s i = 0 := by
  change (if (12339 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 4261441663 12339 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1186 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1186 s i = 0 := by
  change (if (8243 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 4261441663 8243 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1194 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1194 s i = 0 := by
  change (if (51 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 4261441663 51 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1203 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1203 s i = 0 := by
  change (if (23 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 127 23 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1209 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1209 s i = 0 := by
  change (if (55 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 127 55 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1214 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1214 s i = 1 := by
  change (if (1073762323 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 4261441663 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_srai_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_srai_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 4261441663 1073762323 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_srai_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1046 s i commit known, ref_srai_v1052 s i commit known, ref_srai_v1058 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1214 s i commit known, v1215, ref_srai_v1333 s i commit known, ref_srai_v1339 s i commit known, ref_srai_v1345 s i commit known, ref_srai_v1351 s i commit known, ref_srai_v1358 s i commit known, ref_srai_v1365 s i commit known, ref_srai_v1372 s i commit known, ref_srai_v1379 s i commit known, ref_srai_v1386 s i commit known, v1586, v1603, v1604, v1605, v1606, v1607, v1608, v1609, v1610, v1611, v1612, v1613, v1614, v1615, v1616, v1617, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_srai_rd (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) :
    v1320 s i = BitVec.extractLsb' 7 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1046 s i commit known, ref_srai_v1052 s i commit known, ref_srai_v1058 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v1215, v1216, v1217, v1218, v1289, v1290, v1291, v1292, v1293, v1294, v1295, v1296, v1297, v1298, v1299, v1300, v1301, v1302, v1303, v1304, v1305, v1306, v1307, v1308, v1309, v1310, v1311, v1312, v1313, v1314, v1315, v1316, v1317, v1318, v1319, v1320, commit, reference_commit_instruction s i commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 7+j < 12 by omega, show 7+j < 15 by omega, show 7+j < 20 by omega, show 7+j < 21 by omega, show 7+j < 25 by omega, show 7+j < 31 by omega, show 7+j < 32 by omega]
theorem reference_srai_immediate (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) : v2092 s i = immediateI s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_srai_v1046 s i commit known, ref_srai_v1052 s i commit known, ref_srai_v1058 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, ref_srai_v1333 s i commit known, ref_srai_v1339 s i commit known, ref_srai_v1345 s i commit known, ref_srai_v1351 s i commit known, ref_srai_v1358 s i commit known, ref_srai_v1365 s i commit known, ref_srai_v1372 s i commit known, ref_srai_v1379 s i commit known, ref_srai_v1386 s i commit known, v1801, v1819, v1820, v1821, v1822, v1823, v1824, v1825, v1826, v1827, v1828, v1829, v1831, v1832, v2035, v2036, v2037, v2070, v2071, v2072, v2073, v2074, v2075, v2076, v2077, v2078, v2079, v2080, v2081, v2082, v2083, v2084, v2085, v2086, v2087, v2088, v2089, v2090, v2091, v2092, commit, reference_commit_instruction s i commit, BitVec.reduceEq, if_true, if_false]
  rw [reference_sign_extension]
  rfl
theorem reference_srai_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_srai_rs1 s i commit known]
theorem aligned_reference_arithmetic_srai (s : State) (i : Inputs)
    (aligned : DecodedAluAligned s) (agree : RegisterAgreement s)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) :
    s.g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v2316 s i := by
  have arithmetic := decoded_reference_immediate_srai s i s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst
    s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc (referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst)) known
    (reference_srai_immediate s i commit known)
  rw [reference_srai_operand1 s i zero commit known] at arithmetic
  exact (decoded_alu_reference_operands s aligned agree).trans arithmetic
#print axioms aligned_reference_arithmetic_srai
private theorem reference_srai_next_x1 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 1#5) :
    (step s i).g1.r54_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F1 = v2316 s i := by
  change (v2431 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v2312, v2313, v2368, v2369, v2371, v2373, v2375, v2377, v2379, v2381, v2383, v2385, v2387, v2389, v2391, v2393, v2396, v2399, v2401, v2404, v2407, v2409, v2412, v2414, v2416, v2418, v2420, v2422, v2424, v2426, v2428, v2429, v2430, v2431, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x2 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 2#5) :
    (step s i).g1.r55_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F2 = v2316 s i := by
  change (v2585 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v2488, v2489, v2522, v2523, v2525, v2527, v2529, v2531, v2533, v2535, v2537, v2539, v2541, v2543, v2545, v2547, v2550, v2553, v2555, v2558, v2561, v2563, v2566, v2568, v2570, v2572, v2574, v2576, v2578, v2580, v2582, v2583, v2584, v2585, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x3 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 3#5) :
    (step s i).g1.r56_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F3 = v2316 s i := by
  change (v2739 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v2642, v2643, v2676, v2677, v2679, v2681, v2683, v2685, v2687, v2689, v2691, v2693, v2695, v2697, v2699, v2701, v2704, v2707, v2709, v2712, v2715, v2717, v2720, v2722, v2724, v2726, v2728, v2730, v2732, v2734, v2736, v2737, v2738, v2739, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x4 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 4#5) :
    (step s i).g1.r57_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F4 = v2316 s i := by
  change (v2893 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v2796, v2797, v2830, v2831, v2833, v2835, v2837, v2839, v2841, v2843, v2845, v2847, v2849, v2851, v2853, v2855, v2858, v2861, v2863, v2866, v2869, v2871, v2874, v2876, v2878, v2880, v2882, v2884, v2886, v2888, v2890, v2891, v2892, v2893, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x5 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 5#5) :
    (step s i).g1.r58_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F5 = v2316 s i := by
  change (v3047 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v2950, v2951, v2984, v2985, v2987, v2989, v2991, v2993, v2995, v2997, v2999, v3001, v3003, v3005, v3007, v3009, v3012, v3015, v3017, v3020, v3023, v3025, v3028, v3030, v3032, v3034, v3036, v3038, v3040, v3042, v3044, v3045, v3046, v3047, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x6 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 6#5) :
    (step s i).g1.r59_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F6 = v2316 s i := by
  change (v3201 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v3104, v3105, v3138, v3139, v3141, v3143, v3145, v3147, v3149, v3151, v3153, v3155, v3157, v3159, v3161, v3163, v3166, v3169, v3171, v3174, v3177, v3179, v3182, v3184, v3186, v3188, v3190, v3192, v3194, v3196, v3198, v3199, v3200, v3201, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x7 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 7#5) :
    (step s i).g1.r60_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F7 = v2316 s i := by
  change (v3355 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v3258, v3259, v3292, v3293, v3295, v3297, v3299, v3301, v3303, v3305, v3307, v3309, v3311, v3313, v3315, v3317, v3320, v3323, v3325, v3328, v3331, v3333, v3336, v3338, v3340, v3342, v3344, v3346, v3348, v3350, v3352, v3353, v3354, v3355, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x8 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 8#5) :
    (step s i).g1.r61_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F8 = v2316 s i := by
  change (v3509 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v3412, v3413, v3446, v3447, v3449, v3451, v3453, v3455, v3457, v3459, v3461, v3463, v3465, v3467, v3469, v3471, v3474, v3477, v3479, v3482, v3485, v3487, v3490, v3492, v3494, v3496, v3498, v3500, v3502, v3504, v3506, v3507, v3508, v3509, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x9 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 9#5) :
    (step s i).g1.r62_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F9 = v2316 s i := by
  change (v3663 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v3566, v3567, v3600, v3601, v3603, v3605, v3607, v3609, v3611, v3613, v3615, v3617, v3619, v3621, v3623, v3625, v3628, v3631, v3633, v3636, v3639, v3641, v3644, v3646, v3648, v3650, v3652, v3654, v3656, v3658, v3660, v3661, v3662, v3663, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x10 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 10#5) :
    (step s i).g1.r63_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F10 = v2316 s i := by
  change (v3817 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v3720, v3721, v3754, v3755, v3757, v3759, v3761, v3763, v3765, v3767, v3769, v3771, v3773, v3775, v3777, v3779, v3782, v3785, v3787, v3790, v3793, v3795, v3798, v3800, v3802, v3804, v3806, v3808, v3810, v3812, v3814, v3815, v3816, v3817, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x11 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 11#5) :
    (step s i).g2.r64_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F11 = v2316 s i := by
  change (v3971 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v3874, v3875, v3908, v3909, v3911, v3913, v3915, v3917, v3919, v3921, v3923, v3925, v3927, v3929, v3931, v3933, v3936, v3939, v3941, v3944, v3947, v3949, v3952, v3954, v3956, v3958, v3960, v3962, v3964, v3966, v3968, v3969, v3970, v3971, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x12 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 12#5) :
    (step s i).g2.r65_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F12 = v2316 s i := by
  change (v4125 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v4028, v4029, v4062, v4063, v4065, v4067, v4069, v4071, v4073, v4075, v4077, v4079, v4081, v4083, v4085, v4087, v4090, v4093, v4095, v4098, v4101, v4103, v4106, v4108, v4110, v4112, v4114, v4116, v4118, v4120, v4122, v4123, v4124, v4125, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x13 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 13#5) :
    (step s i).g2.r66_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F13 = v2316 s i := by
  change (v4279 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v4182, v4183, v4216, v4217, v4219, v4221, v4223, v4225, v4227, v4229, v4231, v4233, v4235, v4237, v4239, v4241, v4244, v4247, v4249, v4252, v4255, v4257, v4260, v4262, v4264, v4266, v4268, v4270, v4272, v4274, v4276, v4277, v4278, v4279, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x14 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 14#5) :
    (step s i).g2.r67_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F14 = v2316 s i := by
  change (v4433 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v4336, v4337, v4370, v4371, v4373, v4375, v4377, v4379, v4381, v4383, v4385, v4387, v4389, v4391, v4393, v4395, v4398, v4401, v4403, v4406, v4409, v4411, v4414, v4416, v4418, v4420, v4422, v4424, v4426, v4428, v4430, v4431, v4432, v4433, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x15 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 15#5) :
    (step s i).g2.r68_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F15 = v2316 s i := by
  change (v4587 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v4490, v4491, v4524, v4525, v4527, v4529, v4531, v4533, v4535, v4537, v4539, v4541, v4543, v4545, v4547, v4549, v4552, v4555, v4557, v4560, v4563, v4565, v4568, v4570, v4572, v4574, v4576, v4578, v4580, v4582, v4584, v4585, v4586, v4587, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x16 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 16#5) :
    (step s i).g2.r69_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F16 = v2316 s i := by
  change (v4705 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v4617, v4642, v4643, v4645, v4647, v4649, v4651, v4653, v4655, v4657, v4659, v4661, v4663, v4665, v4667, v4670, v4673, v4675, v4678, v4681, v4683, v4686, v4688, v4690, v4692, v4694, v4696, v4698, v4700, v4702, v4703, v4704, v4705, v860, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x17 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 17#5) :
    (step s i).g2.r70_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F17 = v2316 s i := by
  change (v4823 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v4735, v4760, v4761, v4763, v4765, v4767, v4769, v4771, v4773, v4775, v4777, v4779, v4781, v4783, v4785, v4788, v4791, v4793, v4796, v4799, v4801, v4804, v4806, v4808, v4810, v4812, v4814, v4816, v4818, v4820, v4821, v4822, v4823, v866, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x18 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 18#5) :
    (step s i).g2.r71_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F18 = v2316 s i := by
  change (v4941 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v4853, v4878, v4879, v4881, v4883, v4885, v4887, v4889, v4891, v4893, v4895, v4897, v4899, v4901, v4903, v4906, v4909, v4911, v4914, v4917, v4919, v4922, v4924, v4926, v4928, v4930, v4932, v4934, v4936, v4938, v4939, v4940, v4941, v872, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x19 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 19#5) :
    (step s i).g2.r72_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F19 = v2316 s i := by
  change (v5059 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v4971, v4996, v4997, v4999, v5001, v5003, v5005, v5007, v5009, v5011, v5013, v5015, v5017, v5019, v5021, v5024, v5027, v5029, v5032, v5035, v5037, v5040, v5042, v5044, v5046, v5048, v5050, v5052, v5054, v5056, v5057, v5058, v5059, v878, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x20 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 20#5) :
    (step s i).g2.r73_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F20 = v2316 s i := by
  change (v5177 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v5089, v5114, v5115, v5117, v5119, v5121, v5123, v5125, v5127, v5129, v5131, v5133, v5135, v5137, v5139, v5142, v5145, v5147, v5150, v5153, v5155, v5158, v5160, v5162, v5164, v5166, v5168, v5170, v5172, v5174, v5175, v5176, v5177, v884, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x21 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 21#5) :
    (step s i).g2.r74_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F21 = v2316 s i := by
  change (v5295 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v5207, v5232, v5233, v5235, v5237, v5239, v5241, v5243, v5245, v5247, v5249, v5251, v5253, v5255, v5257, v5260, v5263, v5265, v5268, v5271, v5273, v5276, v5278, v5280, v5282, v5284, v5286, v5288, v5290, v5292, v5293, v5294, v5295, v890, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x22 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 22#5) :
    (step s i).g2.r75_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F22 = v2316 s i := by
  change (v5413 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v5325, v5350, v5351, v5353, v5355, v5357, v5359, v5361, v5363, v5365, v5367, v5369, v5371, v5373, v5375, v5378, v5381, v5383, v5386, v5389, v5391, v5394, v5396, v5398, v5400, v5402, v5404, v5406, v5408, v5410, v5411, v5412, v5413, v896, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x23 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 23#5) :
    (step s i).g2.r76_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F23 = v2316 s i := by
  change (v5531 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v5443, v5468, v5469, v5471, v5473, v5475, v5477, v5479, v5481, v5483, v5485, v5487, v5489, v5491, v5493, v5496, v5499, v5501, v5504, v5507, v5509, v5512, v5514, v5516, v5518, v5520, v5522, v5524, v5526, v5528, v5529, v5530, v5531, v902, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x24 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 24#5) :
    (step s i).g2.r77_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F24 = v2316 s i := by
  change (v5649 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v5561, v5586, v5587, v5589, v5591, v5593, v5595, v5597, v5599, v5601, v5603, v5605, v5607, v5609, v5611, v5614, v5617, v5619, v5622, v5625, v5627, v5630, v5632, v5634, v5636, v5638, v5640, v5642, v5644, v5646, v5647, v5648, v5649, v908, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x25 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 25#5) :
    (step s i).g2.r78_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F25 = v2316 s i := by
  change (v5767 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v5679, v5704, v5705, v5707, v5709, v5711, v5713, v5715, v5717, v5719, v5721, v5723, v5725, v5727, v5729, v5732, v5735, v5737, v5740, v5743, v5745, v5748, v5750, v5752, v5754, v5756, v5758, v5760, v5762, v5764, v5765, v5766, v5767, v914, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x26 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 26#5) :
    (step s i).g2.r79_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F26 = v2316 s i := by
  change (v5885 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v5797, v5822, v5823, v5825, v5827, v5829, v5831, v5833, v5835, v5837, v5839, v5841, v5843, v5845, v5847, v5850, v5853, v5855, v5858, v5861, v5863, v5866, v5868, v5870, v5872, v5874, v5876, v5878, v5880, v5882, v5883, v5884, v5885, v920, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x27 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 27#5) :
    (step s i).g2.r80_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F27 = v2316 s i := by
  change (v6003 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v5915, v5940, v5941, v5943, v5945, v5947, v5949, v5951, v5953, v5955, v5957, v5959, v5961, v5963, v5965, v5968, v5971, v5973, v5976, v5979, v5981, v5984, v5986, v5988, v5990, v5992, v5994, v5996, v5998, v6000, v6001, v6002, v6003, v926, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x28 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 28#5) :
    (step s i).g2.r81_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F28 = v2316 s i := by
  change (v6121 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v6033, v6058, v6059, v6061, v6063, v6065, v6067, v6069, v6071, v6073, v6075, v6077, v6079, v6081, v6083, v6086, v6089, v6091, v6094, v6097, v6099, v6102, v6104, v6106, v6108, v6110, v6112, v6114, v6116, v6118, v6119, v6120, v6121, v932, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x29 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 29#5) :
    (step s i).g2.r82_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F29 = v2316 s i := by
  change (v6239 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v6151, v6176, v6177, v6179, v6181, v6183, v6185, v6187, v6189, v6191, v6193, v6195, v6197, v6199, v6201, v6204, v6207, v6209, v6212, v6215, v6217, v6220, v6222, v6224, v6226, v6228, v6230, v6232, v6234, v6236, v6237, v6238, v6239, v938, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x30 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 30#5) :
    (step s i).g2.r83_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F30 = v2316 s i := by
  change (v6357 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v6269, v6294, v6295, v6297, v6299, v6301, v6303, v6305, v6307, v6309, v6311, v6313, v6315, v6317, v6319, v6322, v6325, v6327, v6330, v6333, v6335, v6338, v6340, v6342, v6344, v6346, v6348, v6350, v6352, v6354, v6355, v6356, v6357, v944, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
private theorem reference_srai_next_x31 (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (target : v1320 s i = 31#5) :
    (step s i).g2.r84_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Freg_5F31 = v2316 s i := by
  change (v6475 s i) = v2316 s i
  simp [v0, v1, ref_srai_v1005 s i commit known, ref_srai_v1013 s i commit known, ref_srai_v1021 s i commit known, ref_srai_v1029 s i commit known, ref_srai_v1037 s i commit known, ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, ref_srai_v1106 s i commit known, ref_srai_v1114 s i commit known, ref_srai_v1122 s i commit known, ref_srai_v1130 s i commit known, ref_srai_v1138 s i commit known, ref_srai_v1146 s i commit known, ref_srai_v1154 s i commit known, ref_srai_v1162 s i commit known, ref_srai_v1170 s i commit known, ref_srai_v1178 s i commit known, ref_srai_v1186 s i commit known, ref_srai_v1194 s i commit known, ref_srai_v1203 s i commit known, ref_srai_v1209 s i commit known, ref_srai_v1214 s i commit known, v6387, v6412, v6413, v6415, v6417, v6419, v6421, v6423, v6425, v6427, v6429, v6431, v6433, v6435, v6437, v6440, v6443, v6445, v6448, v6451, v6453, v6456, v6458, v6460, v6462, v6464, v6466, v6468, v6470, v6472, v6473, v6474, v6475, v950, v955, v956, commit, ref_srai_v980 s i commit known, ref_srai_v989 s i commit known, ref_srai_v997 s i commit known, reset, target]
theorem reference_srai_written_value (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) (nonzero : v701 s i ≠ 0) :
    referenceRead (step s i) (v701 s i) = v2316 s i := by
  have bound := (v701 s i).isLt
  have cases : (v701 s i).toNat = 0 ∨ (v701 s i).toNat = 1 ∨ (v701 s i).toNat = 2 ∨ (v701 s i).toNat = 3 ∨ (v701 s i).toNat = 4 ∨ (v701 s i).toNat = 5 ∨ (v701 s i).toNat = 6 ∨ (v701 s i).toNat = 7 ∨ (v701 s i).toNat = 8 ∨ (v701 s i).toNat = 9 ∨ (v701 s i).toNat = 10 ∨ (v701 s i).toNat = 11 ∨ (v701 s i).toNat = 12 ∨ (v701 s i).toNat = 13 ∨ (v701 s i).toNat = 14 ∨ (v701 s i).toNat = 15 ∨ (v701 s i).toNat = 16 ∨ (v701 s i).toNat = 17 ∨ (v701 s i).toNat = 18 ∨ (v701 s i).toNat = 19 ∨ (v701 s i).toNat = 20 ∨ (v701 s i).toNat = 21 ∨ (v701 s i).toNat = 22 ∨ (v701 s i).toNat = 23 ∨ (v701 s i).toNat = 24 ∨ (v701 s i).toNat = 25 ∨ (v701 s i).toNat = 26 ∨ (v701 s i).toNat = 27 ∨ (v701 s i).toNat = 28 ∨ (v701 s i).toNat = 29 ∨ (v701 s i).toNat = 30 ∨ (v701 s i).toNat = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · have target : v701 s i = 0#5 := BitVec.eq_of_toNat_eq h
    exact False.elim (nonzero target)
  · have target : v701 s i = 1#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 1#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x1 s i reset commit known refTarget
  · have target : v701 s i = 2#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 2#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x2 s i reset commit known refTarget
  · have target : v701 s i = 3#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 3#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x3 s i reset commit known refTarget
  · have target : v701 s i = 4#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 4#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x4 s i reset commit known refTarget
  · have target : v701 s i = 5#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 5#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x5 s i reset commit known refTarget
  · have target : v701 s i = 6#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 6#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x6 s i reset commit known refTarget
  · have target : v701 s i = 7#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 7#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x7 s i reset commit known refTarget
  · have target : v701 s i = 8#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 8#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x8 s i reset commit known refTarget
  · have target : v701 s i = 9#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 9#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x9 s i reset commit known refTarget
  · have target : v701 s i = 10#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 10#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x10 s i reset commit known refTarget
  · have target : v701 s i = 11#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 11#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x11 s i reset commit known refTarget
  · have target : v701 s i = 12#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 12#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x12 s i reset commit known refTarget
  · have target : v701 s i = 13#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 13#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x13 s i reset commit known refTarget
  · have target : v701 s i = 14#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 14#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x14 s i reset commit known refTarget
  · have target : v701 s i = 15#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 15#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x15 s i reset commit known refTarget
  · have target : v701 s i = 16#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 16#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x16 s i reset commit known refTarget
  · have target : v701 s i = 17#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 17#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x17 s i reset commit known refTarget
  · have target : v701 s i = 18#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 18#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x18 s i reset commit known refTarget
  · have target : v701 s i = 19#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 19#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x19 s i reset commit known refTarget
  · have target : v701 s i = 20#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 20#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x20 s i reset commit known refTarget
  · have target : v701 s i = 21#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 21#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x21 s i reset commit known refTarget
  · have target : v701 s i = 22#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 22#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x22 s i reset commit known refTarget
  · have target : v701 s i = 23#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 23#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x23 s i reset commit known refTarget
  · have target : v701 s i = 24#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 24#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x24 s i reset commit known refTarget
  · have target : v701 s i = 25#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 25#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x25 s i reset commit known refTarget
  · have target : v701 s i = 26#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 26#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x26 s i reset commit known refTarget
  · have target : v701 s i = 27#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 27#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x27 s i reset commit known refTarget
  · have target : v701 s i = 28#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 28#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x28 s i reset commit known refTarget
  · have target : v701 s i = 29#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 29#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x29 s i reset commit known refTarget
  · have target : v701 s i = 30#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 30#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x30 s i reset commit known refTarget
  · have target : v701 s i = 31#5 := BitVec.eq_of_toNat_eq h
    have refTarget : v1320 s i = 31#5 := (reference_srai_rd s i commit known).trans target
    rw [target]
    exact reference_srai_next_x31 s i reset commit known refTarget
#print axioms reference_srai_written_value
end RiscvMiniProofs
