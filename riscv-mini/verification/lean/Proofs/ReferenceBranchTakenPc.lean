import Proofs.ReferencePcStep
import Proofs.MaskFacts
namespace RiscvMiniProofs
open nCoreSoc
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
private theorem reference_commit_instruction (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v977 s i = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by simp [v977, v975, v974, v973, commit]
private theorem ref_beq_taken_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_taken_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_taken_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_taken_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_taken_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_taken_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_taken_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_beq_taken_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_beq_taken_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_taken_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_taken_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_taken_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_taken_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_taken_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_taken_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_taken_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_taken_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_taken_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_taken_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_taken_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_taken_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_taken_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_taken_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_taken_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1386 s i = 1 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_beq_taken_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_taken_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_taken_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_beq_taken_no_event (s : State) (i : Inputs) (commit : v964 s i = 1)
    (aligned : v6688 s i = 1)
    (taken : v6665 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v6727 s i = 0 := by
  simp only [ref_beq_taken_v1005 s i commit known, ref_beq_taken_v1013 s i commit known, ref_beq_taken_v1021 s i commit known, ref_beq_taken_v1029 s i commit known, ref_beq_taken_v1037 s i commit known, ref_beq_taken_v1046 s i commit known, ref_beq_taken_v1052 s i commit known, ref_beq_taken_v1058 s i commit known, ref_beq_taken_v1066 s i commit known, ref_beq_taken_v1074 s i commit known, ref_beq_taken_v1082 s i commit known, ref_beq_taken_v1090 s i commit known, ref_beq_taken_v1098 s i commit known, ref_beq_taken_v1106 s i commit known, ref_beq_taken_v1114 s i commit known, ref_beq_taken_v1333 s i commit known, ref_beq_taken_v1339 s i commit known, ref_beq_taken_v1345 s i commit known, ref_beq_taken_v1351 s i commit known, ref_beq_taken_v1358 s i commit known, ref_beq_taken_v1365 s i commit known, ref_beq_taken_v1372 s i commit known, ref_beq_taken_v1379 s i commit known, ref_beq_taken_v1386 s i commit known, v4, v6500, v6501, v6502, v6503, v6504, v6505, v6506, v6507, v6508, v6509, v6510, v6511, v6512, v6513, v6514, v6515, v6516, v6517, v6518, v6519, v6520, v6521, v6522, v6523, v6524, v6525, taken, aligned, v6690, v6692, v6693, v6694, v6695, v6698, v6701, v6704, v6707, v6710, v6712, v6714, v6716, v6718, v6720, v6721, v6725, v6726, v6727, commit, ref_beq_taken_v980 s i commit known, ref_beq_taken_v989 s i commit known, ref_beq_taken_v997 s i commit known, BitVec.reduceEq, if_true, if_false]
theorem reference_beq_taken_sequential_select (s : State) (i : Inputs) (commit : v964 s i = 1)
    (aligned : v6688 s i = 1)
    (taken : v6665 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v6832 s i = 1 := by
  simp only [ref_beq_taken_v1351 s i commit known, ref_beq_taken_v1358 s i commit known, ref_beq_taken_v1365 s i commit known, ref_beq_taken_v1372 s i commit known, ref_beq_taken_v1379 s i commit known, ref_beq_taken_v1386 s i commit known, v512, taken, aligned, v6815, v6816, v6817, v6820, v6823, v6826, v6829, v6832, BitVec.reduceEq, if_true, if_false]
theorem reference_beq_taken_control_target (s : State) (i : Inputs) (commit : v964 s i = 1)
    (aligned : v6688 s i = 1)
    (taken : v6665 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v6907 s i = v6875 s i := by
  simp only [ref_beq_taken_v1351 s i commit known, ref_beq_taken_v1358 s i commit known, ref_beq_taken_v1365 s i commit known, ref_beq_taken_v1372 s i commit known, ref_beq_taken_v1379 s i commit known, ref_beq_taken_v1386 s i commit known, taken, aligned, v6890, v6891, v6892, v6895, v6898, v6901, v6904, v6907, BitVec.reduceEq, if_true, if_false]
theorem reference_beq_taken_next_pc (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v6688 s i = 1)
    (taken : v6665 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) :
    (step s i).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc = v6875 s i := by
  rw [reference_pc_no_event s i reset commit (reference_beq_taken_no_event s i commit aligned taken known),
    reference_beq_taken_sequential_select s i commit aligned taken known, if_neg (by decide)]
  exact reference_beq_taken_control_target s i commit aligned taken known
#print axioms reference_beq_taken_next_pc
theorem reference_beq_taken_event_task (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (commit : v964 s i = 1)
    (aligned : v6688 s i = 1)
    (taken : v6665 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : TaskHolds ⟨40, by decide⟩ s i :=
  (event_validity_iff_no_reference_event s i reset env).mpr (reference_beq_taken_no_event s i commit aligned taken known)
#print axioms reference_beq_taken_event_task
private theorem ref_bne_taken_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_taken_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_taken_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_taken_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_taken_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_taken_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_taken_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_bne_taken_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_bne_taken_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_taken_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_taken_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_taken_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_taken_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_taken_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_taken_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_taken_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_taken_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_taken_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_taken_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_taken_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_taken_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_taken_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_taken_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1379 s i = 1 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_bne_taken_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_taken_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_taken_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_taken_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_bne_taken_no_event (s : State) (i : Inputs) (commit : v964 s i = 1)
    (aligned : v6664 s i = 1)
    (taken : v6641 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v6727 s i = 0 := by
  simp only [ref_bne_taken_v1005 s i commit known, ref_bne_taken_v1013 s i commit known, ref_bne_taken_v1021 s i commit known, ref_bne_taken_v1029 s i commit known, ref_bne_taken_v1037 s i commit known, ref_bne_taken_v1046 s i commit known, ref_bne_taken_v1052 s i commit known, ref_bne_taken_v1058 s i commit known, ref_bne_taken_v1066 s i commit known, ref_bne_taken_v1074 s i commit known, ref_bne_taken_v1082 s i commit known, ref_bne_taken_v1090 s i commit known, ref_bne_taken_v1098 s i commit known, ref_bne_taken_v1106 s i commit known, ref_bne_taken_v1114 s i commit known, ref_bne_taken_v1333 s i commit known, ref_bne_taken_v1339 s i commit known, ref_bne_taken_v1345 s i commit known, ref_bne_taken_v1351 s i commit known, ref_bne_taken_v1358 s i commit known, ref_bne_taken_v1365 s i commit known, ref_bne_taken_v1372 s i commit known, ref_bne_taken_v1379 s i commit known, ref_bne_taken_v1386 s i commit known, v4, v6501, v6502, v6503, v6504, v6505, v6506, v6507, v6508, v6509, v6510, v6511, v6512, v6513, v6514, v6515, v6516, v6517, v6518, v6519, v6520, v6521, v6522, v6523, v6524, v6525, taken, aligned, v6690, v6692, v6695, v6696, v6697, v6698, v6701, v6704, v6707, v6710, v6712, v6714, v6716, v6718, v6720, v6721, v6725, v6726, v6727, commit, ref_bne_taken_v980 s i commit known, ref_bne_taken_v989 s i commit known, ref_bne_taken_v997 s i commit known, BitVec.reduceEq, if_true, if_false]
theorem reference_bne_taken_sequential_select (s : State) (i : Inputs) (commit : v964 s i = 1)
    (aligned : v6664 s i = 1)
    (taken : v6641 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v6832 s i = 1 := by
  simp only [ref_bne_taken_v1351 s i commit known, ref_bne_taken_v1358 s i commit known, ref_bne_taken_v1365 s i commit known, ref_bne_taken_v1372 s i commit known, ref_bne_taken_v1379 s i commit known, v512, taken, aligned, v6818, v6819, v6820, v6823, v6826, v6829, v6832, BitVec.reduceEq, if_true, if_false]
theorem reference_bne_taken_control_target (s : State) (i : Inputs) (commit : v964 s i = 1)
    (aligned : v6664 s i = 1)
    (taken : v6641 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v6907 s i = v6871 s i := by
  simp only [ref_bne_taken_v1351 s i commit known, ref_bne_taken_v1358 s i commit known, ref_bne_taken_v1365 s i commit known, ref_bne_taken_v1372 s i commit known, ref_bne_taken_v1379 s i commit known, taken, aligned, v6893, v6894, v6895, v6898, v6901, v6904, v6907, BitVec.reduceEq, if_true, if_false]
theorem reference_bne_taken_next_pc (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v6664 s i = 1)
    (taken : v6641 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) :
    (step s i).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc = v6871 s i := by
  rw [reference_pc_no_event s i reset commit (reference_bne_taken_no_event s i commit aligned taken known),
    reference_bne_taken_sequential_select s i commit aligned taken known, if_neg (by decide)]
  exact reference_bne_taken_control_target s i commit aligned taken known
#print axioms reference_bne_taken_next_pc
theorem reference_bne_taken_event_task (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (commit : v964 s i = 1)
    (aligned : v6664 s i = 1)
    (taken : v6641 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : TaskHolds ⟨40, by decide⟩ s i :=
  (event_validity_iff_no_reference_event s i reset env).mpr (reference_bne_taken_no_event s i commit aligned taken known)
#print axioms reference_bne_taken_event_task
private theorem ref_blt_taken_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_taken_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_taken_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_taken_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_taken_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_taken_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_taken_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_blt_taken_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_blt_taken_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_taken_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_taken_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_taken_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_taken_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_taken_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_taken_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_taken_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_taken_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_taken_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_taken_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_taken_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_taken_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_taken_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1372 s i = 1 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_blt_taken_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_taken_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_taken_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_taken_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_taken_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_blt_taken_no_event (s : State) (i : Inputs) (commit : v964 s i = 1)
    (aligned : v6640 s i = 1)
    (taken : v6617 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v6727 s i = 0 := by
  simp only [ref_blt_taken_v1005 s i commit known, ref_blt_taken_v1013 s i commit known, ref_blt_taken_v1021 s i commit known, ref_blt_taken_v1029 s i commit known, ref_blt_taken_v1037 s i commit known, ref_blt_taken_v1046 s i commit known, ref_blt_taken_v1052 s i commit known, ref_blt_taken_v1058 s i commit known, ref_blt_taken_v1066 s i commit known, ref_blt_taken_v1074 s i commit known, ref_blt_taken_v1082 s i commit known, ref_blt_taken_v1090 s i commit known, ref_blt_taken_v1098 s i commit known, ref_blt_taken_v1106 s i commit known, ref_blt_taken_v1114 s i commit known, ref_blt_taken_v1333 s i commit known, ref_blt_taken_v1339 s i commit known, ref_blt_taken_v1345 s i commit known, ref_blt_taken_v1351 s i commit known, ref_blt_taken_v1358 s i commit known, ref_blt_taken_v1365 s i commit known, ref_blt_taken_v1372 s i commit known, ref_blt_taken_v1379 s i commit known, ref_blt_taken_v1386 s i commit known, v4, v6502, v6503, v6504, v6505, v6506, v6507, v6508, v6509, v6510, v6511, v6512, v6513, v6514, v6515, v6516, v6517, v6518, v6519, v6520, v6521, v6522, v6523, v6524, v6525, taken, aligned, v6690, v6692, v6695, v6698, v6699, v6700, v6701, v6704, v6707, v6710, v6712, v6714, v6716, v6718, v6720, v6721, v6725, v6726, v6727, commit, ref_blt_taken_v980 s i commit known, ref_blt_taken_v989 s i commit known, ref_blt_taken_v997 s i commit known, BitVec.reduceEq, if_true, if_false]
theorem reference_blt_taken_sequential_select (s : State) (i : Inputs) (commit : v964 s i = 1)
    (aligned : v6640 s i = 1)
    (taken : v6617 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v6832 s i = 1 := by
  simp only [ref_blt_taken_v1351 s i commit known, ref_blt_taken_v1358 s i commit known, ref_blt_taken_v1365 s i commit known, ref_blt_taken_v1372 s i commit known, v512, taken, aligned, v6821, v6822, v6823, v6826, v6829, v6832, BitVec.reduceEq, if_true, if_false]
theorem reference_blt_taken_control_target (s : State) (i : Inputs) (commit : v964 s i = 1)
    (aligned : v6640 s i = 1)
    (taken : v6617 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v6907 s i = v6867 s i := by
  simp only [ref_blt_taken_v1351 s i commit known, ref_blt_taken_v1358 s i commit known, ref_blt_taken_v1365 s i commit known, ref_blt_taken_v1372 s i commit known, taken, aligned, v6896, v6897, v6898, v6901, v6904, v6907, BitVec.reduceEq, if_true, if_false]
theorem reference_blt_taken_next_pc (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v6640 s i = 1)
    (taken : v6617 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) :
    (step s i).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc = v6867 s i := by
  rw [reference_pc_no_event s i reset commit (reference_blt_taken_no_event s i commit aligned taken known),
    reference_blt_taken_sequential_select s i commit aligned taken known, if_neg (by decide)]
  exact reference_blt_taken_control_target s i commit aligned taken known
#print axioms reference_blt_taken_next_pc
theorem reference_blt_taken_event_task (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (commit : v964 s i = 1)
    (aligned : v6640 s i = 1)
    (taken : v6617 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : TaskHolds ⟨40, by decide⟩ s i :=
  (event_validity_iff_no_reference_event s i reset env).mpr (reference_blt_taken_no_event s i commit aligned taken known)
#print axioms reference_blt_taken_event_task
private theorem ref_bge_taken_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_taken_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_taken_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_taken_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_taken_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_taken_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_taken_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_bge_taken_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_bge_taken_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_taken_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_taken_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_taken_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_taken_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_taken_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_taken_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_taken_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_taken_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_taken_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_taken_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_taken_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1358 s i = 1 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_bge_taken_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_taken_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_taken_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_taken_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_taken_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_taken_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_taken_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_bge_taken_no_event (s : State) (i : Inputs) (commit : v964 s i = 1)
    (aligned : v6592 s i = 1)
    (taken : v6569 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v6727 s i = 0 := by
  simp only [ref_bge_taken_v1005 s i commit known, ref_bge_taken_v1013 s i commit known, ref_bge_taken_v1021 s i commit known, ref_bge_taken_v1029 s i commit known, ref_bge_taken_v1037 s i commit known, ref_bge_taken_v1046 s i commit known, ref_bge_taken_v1052 s i commit known, ref_bge_taken_v1058 s i commit known, ref_bge_taken_v1066 s i commit known, ref_bge_taken_v1074 s i commit known, ref_bge_taken_v1082 s i commit known, ref_bge_taken_v1090 s i commit known, ref_bge_taken_v1098 s i commit known, ref_bge_taken_v1106 s i commit known, ref_bge_taken_v1114 s i commit known, ref_bge_taken_v1333 s i commit known, ref_bge_taken_v1339 s i commit known, ref_bge_taken_v1345 s i commit known, ref_bge_taken_v1351 s i commit known, ref_bge_taken_v1358 s i commit known, ref_bge_taken_v1365 s i commit known, ref_bge_taken_v1372 s i commit known, ref_bge_taken_v1379 s i commit known, ref_bge_taken_v1386 s i commit known, v4, v6504, v6505, v6506, v6507, v6508, v6509, v6510, v6511, v6512, v6513, v6514, v6515, v6516, v6517, v6518, v6519, v6520, v6521, v6522, v6523, v6524, v6525, taken, aligned, v6690, v6692, v6695, v6698, v6701, v6704, v6705, v6706, v6707, v6710, v6712, v6714, v6716, v6718, v6720, v6721, v6725, v6726, v6727, commit, ref_bge_taken_v980 s i commit known, ref_bge_taken_v989 s i commit known, ref_bge_taken_v997 s i commit known, BitVec.reduceEq, if_true, if_false]
theorem reference_bge_taken_sequential_select (s : State) (i : Inputs) (commit : v964 s i = 1)
    (aligned : v6592 s i = 1)
    (taken : v6569 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v6832 s i = 1 := by
  simp only [ref_bge_taken_v1351 s i commit known, ref_bge_taken_v1358 s i commit known, v512, taken, aligned, v6827, v6828, v6829, v6832, BitVec.reduceEq, if_true, if_false]
theorem reference_bge_taken_control_target (s : State) (i : Inputs) (commit : v964 s i = 1)
    (aligned : v6592 s i = 1)
    (taken : v6569 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v6907 s i = v6859 s i := by
  simp only [ref_bge_taken_v1351 s i commit known, ref_bge_taken_v1358 s i commit known, taken, aligned, v6902, v6903, v6904, v6907, BitVec.reduceEq, if_true, if_false]
theorem reference_bge_taken_next_pc (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v6592 s i = 1)
    (taken : v6569 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) :
    (step s i).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc = v6859 s i := by
  rw [reference_pc_no_event s i reset commit (reference_bge_taken_no_event s i commit aligned taken known),
    reference_bge_taken_sequential_select s i commit aligned taken known, if_neg (by decide)]
  exact reference_bge_taken_control_target s i commit aligned taken known
#print axioms reference_bge_taken_next_pc
theorem reference_bge_taken_event_task (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (commit : v964 s i = 1)
    (aligned : v6592 s i = 1)
    (taken : v6569 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : TaskHolds ⟨40, by decide⟩ s i :=
  (event_validity_iff_no_reference_event s i reset env).mpr (reference_bge_taken_no_event s i commit aligned taken known)
#print axioms reference_bge_taken_event_task
private theorem ref_bltu_taken_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_taken_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_taken_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_taken_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_taken_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_taken_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_taken_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_bltu_taken_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_bltu_taken_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_taken_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_taken_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_taken_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_taken_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_taken_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_taken_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_taken_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_taken_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_taken_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_taken_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_taken_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_taken_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1365 s i = 1 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_bltu_taken_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_taken_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_taken_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_taken_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_taken_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_taken_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_bltu_taken_no_event (s : State) (i : Inputs) (commit : v964 s i = 1)
    (aligned : v6616 s i = 1)
    (taken : v6593 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v6727 s i = 0 := by
  simp only [ref_bltu_taken_v1005 s i commit known, ref_bltu_taken_v1013 s i commit known, ref_bltu_taken_v1021 s i commit known, ref_bltu_taken_v1029 s i commit known, ref_bltu_taken_v1037 s i commit known, ref_bltu_taken_v1046 s i commit known, ref_bltu_taken_v1052 s i commit known, ref_bltu_taken_v1058 s i commit known, ref_bltu_taken_v1066 s i commit known, ref_bltu_taken_v1074 s i commit known, ref_bltu_taken_v1082 s i commit known, ref_bltu_taken_v1090 s i commit known, ref_bltu_taken_v1098 s i commit known, ref_bltu_taken_v1106 s i commit known, ref_bltu_taken_v1114 s i commit known, ref_bltu_taken_v1333 s i commit known, ref_bltu_taken_v1339 s i commit known, ref_bltu_taken_v1345 s i commit known, ref_bltu_taken_v1351 s i commit known, ref_bltu_taken_v1358 s i commit known, ref_bltu_taken_v1365 s i commit known, ref_bltu_taken_v1372 s i commit known, ref_bltu_taken_v1379 s i commit known, ref_bltu_taken_v1386 s i commit known, v4, v6503, v6504, v6505, v6506, v6507, v6508, v6509, v6510, v6511, v6512, v6513, v6514, v6515, v6516, v6517, v6518, v6519, v6520, v6521, v6522, v6523, v6524, v6525, taken, aligned, v6690, v6692, v6695, v6698, v6701, v6702, v6703, v6704, v6707, v6710, v6712, v6714, v6716, v6718, v6720, v6721, v6725, v6726, v6727, commit, ref_bltu_taken_v980 s i commit known, ref_bltu_taken_v989 s i commit known, ref_bltu_taken_v997 s i commit known, BitVec.reduceEq, if_true, if_false]
theorem reference_bltu_taken_sequential_select (s : State) (i : Inputs) (commit : v964 s i = 1)
    (aligned : v6616 s i = 1)
    (taken : v6593 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v6832 s i = 1 := by
  simp only [ref_bltu_taken_v1351 s i commit known, ref_bltu_taken_v1358 s i commit known, ref_bltu_taken_v1365 s i commit known, v512, taken, aligned, v6824, v6825, v6826, v6829, v6832, BitVec.reduceEq, if_true, if_false]
theorem reference_bltu_taken_control_target (s : State) (i : Inputs) (commit : v964 s i = 1)
    (aligned : v6616 s i = 1)
    (taken : v6593 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v6907 s i = v6863 s i := by
  simp only [ref_bltu_taken_v1351 s i commit known, ref_bltu_taken_v1358 s i commit known, ref_bltu_taken_v1365 s i commit known, taken, aligned, v6899, v6900, v6901, v6904, v6907, BitVec.reduceEq, if_true, if_false]
theorem reference_bltu_taken_next_pc (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v6616 s i = 1)
    (taken : v6593 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) :
    (step s i).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc = v6863 s i := by
  rw [reference_pc_no_event s i reset commit (reference_bltu_taken_no_event s i commit aligned taken known),
    reference_bltu_taken_sequential_select s i commit aligned taken known, if_neg (by decide)]
  exact reference_bltu_taken_control_target s i commit aligned taken known
#print axioms reference_bltu_taken_next_pc
theorem reference_bltu_taken_event_task (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (commit : v964 s i = 1)
    (aligned : v6616 s i = 1)
    (taken : v6593 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : TaskHolds ⟨40, by decide⟩ s i :=
  (event_validity_iff_no_reference_event s i reset env).mpr (reference_bltu_taken_no_event s i commit aligned taken known)
#print axioms reference_bltu_taken_event_task
private theorem ref_bgeu_taken_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_taken_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_taken_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_taken_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_taken_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_taken_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_taken_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_bgeu_taken_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_bgeu_taken_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_taken_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_taken_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_taken_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_taken_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_taken_v1106 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1106 s i = 0 := by
  change (if (103 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 103 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_taken_v1114 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1114 s i = 0 := by
  change (if (111 : BitVec 32) = (v977 s i &&& 127) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 127 111 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_taken_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_taken_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_taken_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_taken_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1351 s i = 1 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_bgeu_taken_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_taken_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_taken_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_taken_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_taken_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1386 s i = 0 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 99 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_taken_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_taken_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_taken_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_bgeu_taken_no_event (s : State) (i : Inputs) (commit : v964 s i = 1)
    (aligned : v6568 s i = 1)
    (taken : v6545 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v6727 s i = 0 := by
  simp only [ref_bgeu_taken_v1005 s i commit known, ref_bgeu_taken_v1013 s i commit known, ref_bgeu_taken_v1021 s i commit known, ref_bgeu_taken_v1029 s i commit known, ref_bgeu_taken_v1037 s i commit known, ref_bgeu_taken_v1046 s i commit known, ref_bgeu_taken_v1052 s i commit known, ref_bgeu_taken_v1058 s i commit known, ref_bgeu_taken_v1066 s i commit known, ref_bgeu_taken_v1074 s i commit known, ref_bgeu_taken_v1082 s i commit known, ref_bgeu_taken_v1090 s i commit known, ref_bgeu_taken_v1098 s i commit known, ref_bgeu_taken_v1106 s i commit known, ref_bgeu_taken_v1114 s i commit known, ref_bgeu_taken_v1333 s i commit known, ref_bgeu_taken_v1339 s i commit known, ref_bgeu_taken_v1345 s i commit known, ref_bgeu_taken_v1351 s i commit known, ref_bgeu_taken_v1358 s i commit known, ref_bgeu_taken_v1365 s i commit known, ref_bgeu_taken_v1372 s i commit known, ref_bgeu_taken_v1379 s i commit known, ref_bgeu_taken_v1386 s i commit known, v4, v6505, v6506, v6507, v6508, v6509, v6510, v6511, v6512, v6513, v6514, v6515, v6516, v6517, v6518, v6519, v6520, v6521, v6522, v6523, v6524, v6525, taken, aligned, v6690, v6692, v6695, v6698, v6701, v6704, v6707, v6708, v6709, v6710, v6712, v6714, v6716, v6718, v6720, v6721, v6725, v6726, v6727, commit, ref_bgeu_taken_v980 s i commit known, ref_bgeu_taken_v989 s i commit known, ref_bgeu_taken_v997 s i commit known, BitVec.reduceEq, if_true, if_false]
theorem reference_bgeu_taken_sequential_select (s : State) (i : Inputs) (commit : v964 s i = 1)
    (aligned : v6568 s i = 1)
    (taken : v6545 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v6832 s i = 1 := by
  simp only [ref_bgeu_taken_v1351 s i commit known, v512, taken, aligned, v6830, v6831, v6832, BitVec.reduceEq, if_true, if_false]
theorem reference_bgeu_taken_control_target (s : State) (i : Inputs) (commit : v964 s i = 1)
    (aligned : v6568 s i = 1)
    (taken : v6545 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v6907 s i = v6855 s i := by
  simp only [ref_bgeu_taken_v1351 s i commit known, taken, aligned, v6905, v6906, v6907, BitVec.reduceEq, if_true, if_false]
theorem reference_bgeu_taken_next_pc (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1)
    (aligned : v6568 s i = 1)
    (taken : v6545 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) :
    (step s i).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc = v6855 s i := by
  rw [reference_pc_no_event s i reset commit (reference_bgeu_taken_no_event s i commit aligned taken known),
    reference_bgeu_taken_sequential_select s i commit aligned taken known, if_neg (by decide)]
  exact reference_bgeu_taken_control_target s i commit aligned taken known
#print axioms reference_bgeu_taken_next_pc
theorem reference_bgeu_taken_event_task (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (commit : v964 s i = 1)
    (aligned : v6568 s i = 1)
    (taken : v6545 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : TaskHolds ⟨40, by decide⟩ s i :=
  (event_validity_iff_no_reference_event s i reset env).mpr (reference_bgeu_taken_no_event s i commit aligned taken known)
#print axioms reference_bgeu_taken_event_task
end RiscvMiniProofs
