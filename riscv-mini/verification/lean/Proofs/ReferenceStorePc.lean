import Proofs.ReferencePcStep
import Proofs.MaskFacts
namespace RiscvMiniProofs
open nCoreSoc
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
private theorem reference_commit_instruction (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v977 s i = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by simp [v977, v975, v974, v973, commit]
private theorem ref_sb_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sb_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sb_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sb_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sb_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sb_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sb_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_sb_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_sb_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sb_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sb_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sb_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sb_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sb_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sb_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sb_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1345 s i = 1 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_sb_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sb_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sb_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sb_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sb_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sb_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sb_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sb_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sb_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_sb_no_event (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v6727 s i = 0 := by
  simp only [ref_sb_v1005 s i commit known, ref_sb_v1013 s i commit known, ref_sb_v1021 s i commit known, ref_sb_v1029 s i commit known, ref_sb_v1037 s i commit known, ref_sb_v1046 s i commit known, ref_sb_v1052 s i commit known, ref_sb_v1058 s i commit known, ref_sb_v1066 s i commit known, ref_sb_v1082 s i commit known, ref_sb_v1090 s i commit known, ref_sb_v1106 s i commit known, ref_sb_v1114 s i commit known, ref_sb_v1333 s i commit known, ref_sb_v1339 s i commit known, ref_sb_v1345 s i commit known, ref_sb_v1351 s i commit known, ref_sb_v1358 s i commit known, ref_sb_v1365 s i commit known, ref_sb_v1372 s i commit known, ref_sb_v1379 s i commit known, ref_sb_v1386 s i commit known, v4, v6511, v6512, v6513, v6514, v6515, v6516, v6517, v6518, v6519, v6520, v6521, v6522, v6523, v6524, v6525, v6690, v6692, v6695, v6698, v6701, v6704, v6707, v6710, v6712, v6714, v6716, v6718, v6720, v6721, v6725, v6726, v6727, commit, ref_sb_v980 s i commit known, ref_sb_v989 s i commit known, ref_sb_v997 s i commit known, BitVec.reduceEq, if_true, if_false]
theorem reference_sb_sequential_select (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v6832 s i = 0 := by
  simp only [ref_sb_v1106 s i commit known, ref_sb_v1114 s i commit known, ref_sb_v1351 s i commit known, ref_sb_v1358 s i commit known, ref_sb_v1365 s i commit known, ref_sb_v1372 s i commit known, ref_sb_v1379 s i commit known, ref_sb_v1386 s i commit known, v4, v6812, v6814, v6817, v6820, v6823, v6826, v6829, v6832, BitVec.reduceEq, if_true, if_false]
theorem reference_sb_next_pc (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) :
    (step s i).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc = v2222 s i + 4 := by
  rw [reference_pc_no_event s i reset commit (reference_sb_no_event s i commit known),
    reference_sb_sequential_select s i commit known, if_pos rfl]
#print axioms reference_sb_next_pc
theorem reference_sb_event_task (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : TaskHolds ⟨40, by decide⟩ s i :=
  (event_validity_iff_no_reference_event s i reset env).mpr (reference_sb_no_event s i commit known)
#print axioms reference_sb_event_task
private theorem ref_sh_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sh_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sh_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sh_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sh_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sh_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sh_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_sh_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_sh_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sh_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sh_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sh_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sh_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sh_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sh_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v1339 s i = 1 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_sh_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sh_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sh_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sh_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sh_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sh_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sh_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sh_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sh_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_sh_no_event (s : State) (i : Inputs) (commit : v964 s i = 1)
    (aligned : v6544 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v6727 s i = 0 := by
  simp only [ref_sh_v1005 s i commit known, ref_sh_v1013 s i commit known, ref_sh_v1021 s i commit known, ref_sh_v1029 s i commit known, ref_sh_v1037 s i commit known, ref_sh_v1046 s i commit known, ref_sh_v1052 s i commit known, ref_sh_v1058 s i commit known, ref_sh_v1066 s i commit known, ref_sh_v1082 s i commit known, ref_sh_v1090 s i commit known, ref_sh_v1106 s i commit known, ref_sh_v1114 s i commit known, ref_sh_v1333 s i commit known, ref_sh_v1339 s i commit known, ref_sh_v1351 s i commit known, ref_sh_v1358 s i commit known, ref_sh_v1365 s i commit known, ref_sh_v1372 s i commit known, ref_sh_v1379 s i commit known, ref_sh_v1386 s i commit known, v4, v6512, v6513, v6514, v6515, v6516, v6517, v6518, v6519, v6520, v6521, v6522, v6523, v6524, v6525, aligned, v6690, v6692, v6695, v6698, v6701, v6704, v6707, v6710, v6712, v6714, v6716, v6717, v6718, v6720, v6721, v6725, v6726, v6727, commit, ref_sh_v980 s i commit known, ref_sh_v989 s i commit known, ref_sh_v997 s i commit known, BitVec.reduceEq, if_true, if_false]
theorem reference_sh_sequential_select (s : State) (i : Inputs) (commit : v964 s i = 1)
    (aligned : v6544 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v6832 s i = 0 := by
  simp only [ref_sh_v1106 s i commit known, ref_sh_v1114 s i commit known, ref_sh_v1351 s i commit known, ref_sh_v1358 s i commit known, ref_sh_v1365 s i commit known, ref_sh_v1372 s i commit known, ref_sh_v1379 s i commit known, ref_sh_v1386 s i commit known, v4, v6812, v6814, v6817, v6820, v6823, v6826, v6829, v6832, BitVec.reduceEq, if_true, if_false]
theorem reference_sh_next_pc (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v6544 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) :
    (step s i).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc = v2222 s i + 4 := by
  rw [reference_pc_no_event s i reset commit (reference_sh_no_event s i commit aligned known),
    reference_sh_sequential_select s i commit aligned known, if_pos rfl]
#print axioms reference_sh_next_pc
theorem reference_sh_event_task (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (commit : v964 s i = 1)
    (aligned : v6544 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : TaskHolds ⟨40, by decide⟩ s i :=
  (event_validity_iff_no_reference_event s i reset env).mpr (reference_sh_no_event s i commit aligned known)
#print axioms reference_sh_event_task
private theorem ref_sw_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sw_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sw_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sw_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sw_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sw_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sw_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_sw_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_sw_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sw_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sw_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sw_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sw_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sw_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1333 s i = 1 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_sw_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sw_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sw_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sw_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sw_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sw_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sw_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sw_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sw_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sw_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_sw_no_event (s : State) (i : Inputs) (commit : v964 s i = 1)
    (aligned : v6538 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v6727 s i = 0 := by
  simp only [ref_sw_v1005 s i commit known, ref_sw_v1013 s i commit known, ref_sw_v1021 s i commit known, ref_sw_v1029 s i commit known, ref_sw_v1037 s i commit known, ref_sw_v1046 s i commit known, ref_sw_v1052 s i commit known, ref_sw_v1058 s i commit known, ref_sw_v1066 s i commit known, ref_sw_v1082 s i commit known, ref_sw_v1090 s i commit known, ref_sw_v1106 s i commit known, ref_sw_v1114 s i commit known, ref_sw_v1333 s i commit known, ref_sw_v1339 s i commit known, ref_sw_v1351 s i commit known, ref_sw_v1358 s i commit known, ref_sw_v1365 s i commit known, ref_sw_v1372 s i commit known, ref_sw_v1379 s i commit known, ref_sw_v1386 s i commit known, v4, v6513, v6514, v6515, v6516, v6517, v6518, v6519, v6520, v6521, v6522, v6523, v6524, v6525, aligned, v6690, v6692, v6695, v6698, v6701, v6704, v6707, v6710, v6712, v6714, v6716, v6718, v6719, v6720, v6721, v6725, v6726, v6727, commit, ref_sw_v980 s i commit known, ref_sw_v989 s i commit known, ref_sw_v997 s i commit known, BitVec.reduceEq, if_true, if_false]
theorem reference_sw_sequential_select (s : State) (i : Inputs) (commit : v964 s i = 1)
    (aligned : v6538 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v6832 s i = 0 := by
  simp only [ref_sw_v1106 s i commit known, ref_sw_v1114 s i commit known, ref_sw_v1351 s i commit known, ref_sw_v1358 s i commit known, ref_sw_v1365 s i commit known, ref_sw_v1372 s i commit known, ref_sw_v1379 s i commit known, ref_sw_v1386 s i commit known, v4, v6812, v6814, v6817, v6820, v6823, v6826, v6829, v6832, BitVec.reduceEq, if_true, if_false]
theorem reference_sw_next_pc (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v6538 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) :
    (step s i).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc = v2222 s i + 4 := by
  rw [reference_pc_no_event s i reset commit (reference_sw_no_event s i commit aligned known),
    reference_sw_sequential_select s i commit aligned known, if_pos rfl]
#print axioms reference_sw_next_pc
theorem reference_sw_event_task (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (commit : v964 s i = 1)
    (aligned : v6538 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : TaskHolds ⟨40, by decide⟩ s i :=
  (event_validity_iff_no_reference_event s i reset env).mpr (reference_sw_no_event s i commit aligned known)
#print axioms reference_sw_event_task
end RiscvMiniProofs
