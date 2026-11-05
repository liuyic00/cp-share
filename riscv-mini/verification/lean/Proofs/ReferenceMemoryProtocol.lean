import Proofs.ReferencePcStep
import Proofs.MaskFacts
namespace RiscvMiniProofs
open nCoreSoc
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false
private theorem reference_commit_instruction (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v977 s i = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by simp [v977, v975, v974, v973, commit]
private theorem ref_memory_address_v2108 (s : State) (i : Inputs) : v2108 s i = v2095 s i := rfl
private theorem ref_memory_address_v2123 (s : State) (i : Inputs) : v2123 s i = v2095 s i := rfl
private theorem ref_memory_address_v2145 (s : State) (i : Inputs) : v2145 s i = v2095 s i := rfl
private theorem ref_memory_address_v2165 (s : State) (i : Inputs) : v2165 s i = v2095 s i := rfl
private theorem ref_memory_address_v2182 (s : State) (i : Inputs) : v2182 s i = v2095 s i := rfl
private theorem ref_memory_address_v7124 (s : State) (i : Inputs) : v7124 s i = v2095 s i := rfl
private theorem ref_memory_address_v7133 (s : State) (i : Inputs) : v7133 s i = v2095 s i := rfl
private theorem ref_memory_address_v7142 (s : State) (i : Inputs) : v7142 s i = v2095 s i := rfl
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
theorem reference_lui_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 55) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_lui_v1066 s i commit known, ref_lui_v1074 s i commit known, ref_lui_v1082 s i commit known, ref_lui_v1090 s i commit known, ref_lui_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_lui_v1333 s i commit known, ref_lui_v1339 s i commit known, ref_lui_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_lui_v1333 s i commit known, ref_lui_v1339 s i commit known, ref_lui_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_lui_memory_protocol
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
theorem reference_auipc_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 23) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_auipc_v1066 s i commit known, ref_auipc_v1074 s i commit known, ref_auipc_v1082 s i commit known, ref_auipc_v1090 s i commit known, ref_auipc_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_auipc_v1333 s i commit known, ref_auipc_v1339 s i commit known, ref_auipc_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_auipc_v1333 s i commit known, ref_auipc_v1339 s i commit known, ref_auipc_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_auipc_memory_protocol
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
theorem reference_jal_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_jal_v1066 s i commit known, ref_jal_v1074 s i commit known, ref_jal_v1082 s i commit known, ref_jal_v1090 s i commit known, ref_jal_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_jal_v1333 s i commit known, ref_jal_v1339 s i commit known, ref_jal_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_jal_v1333 s i commit known, ref_jal_v1339 s i commit known, ref_jal_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_jal_memory_protocol
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
theorem reference_jalr_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_jalr_v1066 s i commit known, ref_jalr_v1074 s i commit known, ref_jalr_v1082 s i commit known, ref_jalr_v1090 s i commit known, ref_jalr_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_jalr_v1333 s i commit known, ref_jalr_v1339 s i commit known, ref_jalr_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_jalr_v1333 s i commit known, ref_jalr_v1339 s i commit known, ref_jalr_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_jalr_memory_protocol
private theorem ref_beq_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_beq_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_beq_v1066 s i commit known, ref_beq_v1074 s i commit known, ref_beq_v1082 s i commit known, ref_beq_v1090 s i commit known, ref_beq_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_beq_v1066 s i commit known, ref_beq_v1074 s i commit known, ref_beq_v1082 s i commit known, ref_beq_v1090 s i commit known, ref_beq_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_beq_v1333 s i commit known, ref_beq_v1339 s i commit known, ref_beq_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_beq_v1333 s i commit known, ref_beq_v1339 s i commit known, ref_beq_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_beq_memory_protocol
private theorem ref_bne_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_bne_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_bne_v1066 s i commit known, ref_bne_v1074 s i commit known, ref_bne_v1082 s i commit known, ref_bne_v1090 s i commit known, ref_bne_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_bne_v1066 s i commit known, ref_bne_v1074 s i commit known, ref_bne_v1082 s i commit known, ref_bne_v1090 s i commit known, ref_bne_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_bne_v1333 s i commit known, ref_bne_v1339 s i commit known, ref_bne_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_bne_v1333 s i commit known, ref_bne_v1339 s i commit known, ref_bne_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_bne_memory_protocol
private theorem ref_blt_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_blt_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_blt_v1066 s i commit known, ref_blt_v1074 s i commit known, ref_blt_v1082 s i commit known, ref_blt_v1090 s i commit known, ref_blt_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_blt_v1066 s i commit known, ref_blt_v1074 s i commit known, ref_blt_v1082 s i commit known, ref_blt_v1090 s i commit known, ref_blt_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_blt_v1333 s i commit known, ref_blt_v1339 s i commit known, ref_blt_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_blt_v1333 s i commit known, ref_blt_v1339 s i commit known, ref_blt_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_blt_memory_protocol
private theorem ref_bge_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_bge_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_bge_v1066 s i commit known, ref_bge_v1074 s i commit known, ref_bge_v1082 s i commit known, ref_bge_v1090 s i commit known, ref_bge_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_bge_v1066 s i commit known, ref_bge_v1074 s i commit known, ref_bge_v1082 s i commit known, ref_bge_v1090 s i commit known, ref_bge_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_bge_v1333 s i commit known, ref_bge_v1339 s i commit known, ref_bge_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_bge_v1333 s i commit known, ref_bge_v1339 s i commit known, ref_bge_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_bge_memory_protocol
private theorem ref_bltu_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_bltu_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_bltu_v1066 s i commit known, ref_bltu_v1074 s i commit known, ref_bltu_v1082 s i commit known, ref_bltu_v1090 s i commit known, ref_bltu_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_bltu_v1066 s i commit known, ref_bltu_v1074 s i commit known, ref_bltu_v1082 s i commit known, ref_bltu_v1090 s i commit known, ref_bltu_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_bltu_v1333 s i commit known, ref_bltu_v1339 s i commit known, ref_bltu_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_bltu_v1333 s i commit known, ref_bltu_v1339 s i commit known, ref_bltu_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_bltu_memory_protocol
private theorem ref_bgeu_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 16387 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_v1082 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1082 s i = 0 := by
  change (if (8195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 8195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_v1090 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1090 s i = 0 := by
  change (if (4099 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 4099 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_bgeu_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_bgeu_v1066 s i commit known, ref_bgeu_v1074 s i commit known, ref_bgeu_v1082 s i commit known, ref_bgeu_v1090 s i commit known, ref_bgeu_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_bgeu_v1066 s i commit known, ref_bgeu_v1074 s i commit known, ref_bgeu_v1082 s i commit known, ref_bgeu_v1090 s i commit known, ref_bgeu_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_bgeu_v1333 s i commit known, ref_bgeu_v1339 s i commit known, ref_bgeu_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_bgeu_v1333 s i commit known, ref_bgeu_v1339 s i commit known, ref_bgeu_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_bgeu_memory_protocol
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
private theorem ref_lb_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 3 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lb_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 3 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lb_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 3 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_lb_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) :
    v9166 s i = 1 ∧ v9190 s i = 8 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, v8609, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_lb_v1333 s i commit known, ref_lb_v1339 s i commit known, ref_lb_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_lb_v1333 s i commit known, ref_lb_v1339 s i commit known, ref_lb_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_lb_memory_protocol
theorem reference_lb_memory_address (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 3) : v9171 s i = v2095 s i := by
  simp only [ref_lb_v1066 s i commit known, ref_lb_v1074 s i commit known, ref_lb_v1082 s i commit known, ref_lb_v1090 s i commit known, ref_lb_v1098 s i commit known, ref_memory_address_v2182 s i, v7164, v7165, v7166, v7167, v7168, v7169, v9170, v9171, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_lb_memory_address
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
private theorem ref_lh_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4099 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lh_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4099 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_lh_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4099 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
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
private theorem ref_lh_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4099 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lh_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4099 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lh_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4099 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
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
theorem reference_lh_memory_guard (s : State) (i : Inputs)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) : v2159 s i = 1 := by
  rcases BitVec.eq_zero_or_eq_one (v2159 s i) with bad | good
  · simp only [ref_lh_v1005 s i commit known, ref_lh_v1013 s i commit known, ref_lh_v1021 s i commit known, ref_lh_v1029 s i commit known, ref_lh_v1037 s i commit known, ref_lh_v1046 s i commit known, ref_lh_v1052 s i commit known, ref_lh_v1058 s i commit known, ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, ref_lh_v1333 s i commit known, ref_lh_v1339 s i commit known, ref_lh_v1345 s i commit known, bad, v4, v512, v6507, v6508, v6509, v6510, v6511, v6512, v6513, v6514, v6515, v6516, v6517, v6518, v6519, v6520, v6521, v6522, v6523, v6524, v6525, v6711, v6712, v6714, v6716, v6718, v6720, v6721, v6725, v6726, v6727, commit, ref_lh_v980 s i commit known, ref_lh_v989 s i commit known, ref_lh_v997 s i commit known, BitVec.reduceEq, if_true, if_false] at event
    all_goals contradiction
  · exact good
theorem reference_lh_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (aligned : v2159 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) :
    v9166 s i = 1 ∧ v9190 s i = 16 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v512, v9157, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, v9179, v9181, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_lh_v1333 s i commit known, ref_lh_v1339 s i commit known, ref_lh_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_lh_v1333 s i commit known, ref_lh_v1339 s i commit known, ref_lh_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_lh_memory_protocol
theorem reference_lh_memory_address (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (aligned : v2159 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4099) : v9171 s i = v2095 s i := by
  simp only [ref_lh_v1066 s i commit known, ref_lh_v1074 s i commit known, ref_lh_v1082 s i commit known, ref_lh_v1090 s i commit known, aligned, ref_memory_address_v2165 s i, v7163, v7165, v7166, v7167, v7168, v7169, v9170, v9171, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_lh_memory_address
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
private theorem ref_lw_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8195 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lw_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8195 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_lw_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8195 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
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
private theorem ref_lw_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8195 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lw_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8195 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lw_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8195 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
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
theorem reference_lw_memory_guard (s : State) (i : Inputs)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) : v2139 s i = 1 := by
  rcases BitVec.eq_zero_or_eq_one (v2139 s i) with bad | good
  · simp only [ref_lw_v1005 s i commit known, ref_lw_v1013 s i commit known, ref_lw_v1021 s i commit known, ref_lw_v1029 s i commit known, ref_lw_v1037 s i commit known, ref_lw_v1046 s i commit known, ref_lw_v1052 s i commit known, ref_lw_v1058 s i commit known, ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, ref_lw_v1333 s i commit known, ref_lw_v1339 s i commit known, ref_lw_v1345 s i commit known, bad, v4, v512, v6508, v6509, v6510, v6511, v6512, v6513, v6514, v6515, v6516, v6517, v6518, v6519, v6520, v6521, v6522, v6523, v6524, v6525, v6713, v6714, v6716, v6718, v6720, v6721, v6725, v6726, v6727, commit, ref_lw_v980 s i commit known, ref_lw_v989 s i commit known, ref_lw_v997 s i commit known, BitVec.reduceEq, if_true, if_false] at event
    all_goals contradiction
  · exact good
theorem reference_lw_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (aligned : v2139 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) :
    v9166 s i = 1 ∧ v9190 s i = 32 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v512, v9159, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, v8605, v9183, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_lw_v1333 s i commit known, ref_lw_v1339 s i commit known, ref_lw_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_lw_v1333 s i commit known, ref_lw_v1339 s i commit known, ref_lw_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_lw_memory_protocol
theorem reference_lw_memory_address (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (aligned : v2139 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8195) : v9171 s i = v2095 s i := by
  simp only [ref_lw_v1066 s i commit known, ref_lw_v1074 s i commit known, ref_lw_v1082 s i commit known, aligned, ref_memory_address_v2145 s i, v7158, v7166, v7167, v7168, v7169, v9170, v9171, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_lw_memory_address
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
private theorem ref_lbu_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16387 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lbu_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16387 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lbu_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16387 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_lbu_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) :
    v9166 s i = 1 ∧ v9190 s i = 8 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v512, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, v9178, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_lbu_v1333 s i commit known, ref_lbu_v1339 s i commit known, ref_lbu_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_lbu_v1333 s i commit known, ref_lbu_v1339 s i commit known, ref_lbu_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_lbu_memory_protocol
theorem reference_lbu_memory_address (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16387) : v9171 s i = v2095 s i := by
  simp only [ref_lbu_v1066 s i commit known, ref_lbu_v1074 s i commit known, ref_memory_address_v2123 s i, v7167, v7168, v7169, v9170, v9171, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_lbu_memory_address
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
private theorem ref_lhu_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20483 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lhu_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20483 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_lhu_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20483 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_lhu_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) : v1066 s i = 1 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20483 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_lhu_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) : v1333 s i = 0 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20483 28799 8227 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lhu_v1339 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) : v1339 s i = 0 := by
  change (if (4131 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20483 28799 4131 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_lhu_v1345 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) : v1345 s i = 0 := by
  change (if (35 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20483 28799 35 known (by decide)
  rw [if_neg (Ne.symm no)]
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
theorem reference_lhu_memory_guard (s : State) (i : Inputs)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) : v2097 s i = 1 := by
  rcases BitVec.eq_zero_or_eq_one (v2097 s i) with bad | good
  · simp only [ref_lhu_v1005 s i commit known, ref_lhu_v1013 s i commit known, ref_lhu_v1021 s i commit known, ref_lhu_v1029 s i commit known, ref_lhu_v1037 s i commit known, ref_lhu_v1046 s i commit known, ref_lhu_v1052 s i commit known, ref_lhu_v1058 s i commit known, ref_lhu_v1066 s i commit known, ref_lhu_v1333 s i commit known, ref_lhu_v1339 s i commit known, ref_lhu_v1345 s i commit known, bad, v4, v512, v6510, v6511, v6512, v6513, v6514, v6515, v6516, v6517, v6518, v6519, v6520, v6521, v6522, v6523, v6524, v6525, v6715, v6716, v6718, v6720, v6721, v6725, v6726, v6727, commit, ref_lhu_v980 s i commit known, ref_lhu_v989 s i commit known, ref_lhu_v997 s i commit known, BitVec.reduceEq, if_true, if_false] at event
    all_goals contradiction
  · exact good
theorem reference_lhu_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (aligned : v2097 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) :
    v9166 s i = 1 ∧ v9190 s i = 16 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_lhu_v1066 s i commit known, aligned, v512, v9162, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_lhu_v1066 s i commit known, aligned, v9177, v9186, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_lhu_v1333 s i commit known, ref_lhu_v1339 s i commit known, ref_lhu_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_lhu_v1333 s i commit known, ref_lhu_v1339 s i commit known, ref_lhu_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_lhu_memory_protocol
theorem reference_lhu_memory_address (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (aligned : v2097 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20483) : v9171 s i = v2095 s i := by
  simp only [ref_lhu_v1066 s i commit known, aligned, ref_memory_address_v2108 s i, v7153, v7168, v7169, v9170, v9171, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_lhu_memory_address
private theorem ref_sb_v1066 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1066 s i = 0 := by
  change (if (20483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 28799 20483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sb_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 28799 16387 known (by decide)
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
private theorem ref_sb_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 35 28799 3 known (by decide)
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
theorem reference_sb_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 1 ∧ v9263 s i = 8 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_sb_v1066 s i commit known, ref_sb_v1074 s i commit known, ref_sb_v1082 s i commit known, ref_sb_v1090 s i commit known, ref_sb_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sb_v1066 s i commit known, ref_sb_v1074 s i commit known, ref_sb_v1082 s i commit known, ref_sb_v1090 s i commit known, ref_sb_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sb_v1333 s i commit known, ref_sb_v1339 s i commit known, ref_sb_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sb_v1333 s i commit known, ref_sb_v1339 s i commit known, ref_sb_v1345 s i commit known, v9255, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_sb_memory_protocol
theorem reference_sb_memory_address (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v9208 s i = v2095 s i := by
  simp only [ref_sb_v1333 s i commit known, ref_sb_v1339 s i commit known, ref_sb_v1345 s i commit known, ref_memory_address_v7142 s i, v7143, v7144, v7145, v7146, v9207, v9208, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_sb_memory_address
theorem reference_sb_store_data (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v9249 s i = (0#24) ++ (BitVec.extractLsb' 0 8 (v1539 s i)) := by
  simp only [ref_sb_v1333 s i commit known, ref_sb_v1339 s i commit known, ref_sb_v1345 s i commit known, v225, v9240, v9241, v9242, v9244, v9246, v9247, v9248, v9249, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_sb_store_data
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
private theorem ref_sh_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 28799 16387 known (by decide)
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
private theorem ref_sh_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4131 28799 3 known (by decide)
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
theorem reference_sh_memory_guard (s : State) (i : Inputs)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v6544 s i = 1 := by
  rcases BitVec.eq_zero_or_eq_one (v6544 s i) with bad | good
  · simp only [ref_sh_v1005 s i commit known, ref_sh_v1013 s i commit known, ref_sh_v1021 s i commit known, ref_sh_v1029 s i commit known, ref_sh_v1037 s i commit known, ref_sh_v1046 s i commit known, ref_sh_v1052 s i commit known, ref_sh_v1058 s i commit known, ref_sh_v1333 s i commit known, ref_sh_v1339 s i commit known, v4, v512, v6512, v6513, v6514, v6515, v6516, v6517, v6518, v6519, v6520, v6521, v6522, v6523, v6524, v6525, bad, v6717, v6718, v6720, v6721, v6725, v6726, v6727, commit, ref_sh_v980 s i commit known, ref_sh_v989 s i commit known, ref_sh_v997 s i commit known, BitVec.reduceEq, if_true, if_false] at event
    all_goals contradiction
  · exact good
theorem reference_sh_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (aligned : v6544 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 1 ∧ v9263 s i = 16 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_sh_v1066 s i commit known, ref_sh_v1074 s i commit known, ref_sh_v1082 s i commit known, ref_sh_v1090 s i commit known, ref_sh_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sh_v1066 s i commit known, ref_sh_v1074 s i commit known, ref_sh_v1082 s i commit known, ref_sh_v1090 s i commit known, ref_sh_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sh_v1333 s i commit known, ref_sh_v1339 s i commit known, v512, aligned, v9197, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sh_v1333 s i commit known, ref_sh_v1339 s i commit known, aligned, v9254, v9257, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_sh_memory_protocol
theorem reference_sh_memory_address (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (aligned : v6544 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v9208 s i = v2095 s i := by
  simp only [ref_sh_v1333 s i commit known, ref_sh_v1339 s i commit known, aligned, ref_memory_address_v7133 s i, v7138, v7144, v7145, v7146, v9207, v9208, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_sh_memory_address
theorem reference_sh_store_data (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (aligned : v6544 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v9249 s i = (0#16) ++ (BitVec.extractLsb' 0 16 (v1539 s i)) := by
  simp only [ref_sh_v1333 s i commit known, ref_sh_v1339 s i commit known, v2100, aligned, v9238, v9239, v9243, v9244, v9246, v9247, v9248, v9249, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_sh_store_data
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
private theorem ref_sw_v1074 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1074 s i = 0 := by
  change (if (16387 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 28799 16387 known (by decide)
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
private theorem ref_sw_v1098 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1098 s i = 0 := by
  change (if (3 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 28799 3 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_sw_v1333 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v1333 s i = 1 := by
  change (if (8227 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 8227 28799 known (by decide)
  rw [if_pos yes.symm]
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
theorem reference_sw_memory_guard (s : State) (i : Inputs)
    (commit : v964 s i = 1) (event : v6727 s i = 0)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v6538 s i = 1 := by
  rcases BitVec.eq_zero_or_eq_one (v6538 s i) with bad | good
  · simp only [ref_sw_v1005 s i commit known, ref_sw_v1013 s i commit known, ref_sw_v1021 s i commit known, ref_sw_v1029 s i commit known, ref_sw_v1037 s i commit known, ref_sw_v1046 s i commit known, ref_sw_v1052 s i commit known, ref_sw_v1058 s i commit known, ref_sw_v1333 s i commit known, v4, v512, v6513, v6514, v6515, v6516, v6517, v6518, v6519, v6520, v6521, v6522, v6523, v6524, v6525, bad, v6719, v6720, v6721, v6725, v6726, v6727, commit, ref_sw_v980 s i commit known, ref_sw_v989 s i commit known, ref_sw_v997 s i commit known, BitVec.reduceEq, if_true, if_false] at event
    all_goals contradiction
  · exact good
theorem reference_sw_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (aligned : v6538 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 1 ∧ v9263 s i = 32 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_sw_v1066 s i commit known, ref_sw_v1074 s i commit known, ref_sw_v1082 s i commit known, ref_sw_v1090 s i commit known, ref_sw_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sw_v1066 s i commit known, ref_sw_v1074 s i commit known, ref_sw_v1082 s i commit known, ref_sw_v1090 s i commit known, ref_sw_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sw_v1333 s i commit known, v512, aligned, v9199, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sw_v1333 s i commit known, aligned, v8605, v9259, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_sw_memory_protocol
theorem reference_sw_memory_address (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (aligned : v6538 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v9208 s i = v2095 s i := by
  simp only [ref_sw_v1333 s i commit known, aligned, ref_memory_address_v7124 s i, v7129, v7145, v7146, v9207, v9208, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_sw_memory_address
theorem reference_sw_store_data (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (aligned : v6538 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v9249 s i = v1539 s i := by
  simp only [ref_sw_v1333 s i commit known, aligned, v9245, v9246, v9247, v9248, v9249, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_sw_store_data
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
theorem reference_addi_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 19) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_addi_v1066 s i commit known, ref_addi_v1074 s i commit known, ref_addi_v1082 s i commit known, ref_addi_v1090 s i commit known, ref_addi_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_addi_v1333 s i commit known, ref_addi_v1339 s i commit known, ref_addi_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_addi_v1333 s i commit known, ref_addi_v1339 s i commit known, ref_addi_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_addi_memory_protocol
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
theorem reference_slti_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8211) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_slti_v1066 s i commit known, ref_slti_v1074 s i commit known, ref_slti_v1082 s i commit known, ref_slti_v1090 s i commit known, ref_slti_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_slti_v1333 s i commit known, ref_slti_v1339 s i commit known, ref_slti_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_slti_v1333 s i commit known, ref_slti_v1339 s i commit known, ref_slti_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_slti_memory_protocol
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
theorem reference_sltiu_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 12307) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sltiu_v1066 s i commit known, ref_sltiu_v1074 s i commit known, ref_sltiu_v1082 s i commit known, ref_sltiu_v1090 s i commit known, ref_sltiu_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sltiu_v1333 s i commit known, ref_sltiu_v1339 s i commit known, ref_sltiu_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sltiu_v1333 s i commit known, ref_sltiu_v1339 s i commit known, ref_sltiu_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_sltiu_memory_protocol
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
theorem reference_xori_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16403) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_xori_v1066 s i commit known, ref_xori_v1074 s i commit known, ref_xori_v1082 s i commit known, ref_xori_v1090 s i commit known, ref_xori_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_xori_v1333 s i commit known, ref_xori_v1339 s i commit known, ref_xori_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_xori_v1333 s i commit known, ref_xori_v1339 s i commit known, ref_xori_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_xori_memory_protocol
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
theorem reference_ori_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24595) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_ori_v1066 s i commit known, ref_ori_v1074 s i commit known, ref_ori_v1082 s i commit known, ref_ori_v1090 s i commit known, ref_ori_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_ori_v1333 s i commit known, ref_ori_v1339 s i commit known, ref_ori_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_ori_v1333 s i commit known, ref_ori_v1339 s i commit known, ref_ori_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_ori_memory_protocol
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
theorem reference_andi_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28691) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_andi_v1066 s i commit known, ref_andi_v1074 s i commit known, ref_andi_v1082 s i commit known, ref_andi_v1090 s i commit known, ref_andi_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_andi_v1333 s i commit known, ref_andi_v1339 s i commit known, ref_andi_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_andi_v1333 s i commit known, ref_andi_v1339 s i commit known, ref_andi_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_andi_memory_protocol
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
theorem reference_slli_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4115) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_slli_v1066 s i commit known, ref_slli_v1074 s i commit known, ref_slli_v1082 s i commit known, ref_slli_v1090 s i commit known, ref_slli_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_slli_v1333 s i commit known, ref_slli_v1339 s i commit known, ref_slli_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_slli_v1333 s i commit known, ref_slli_v1339 s i commit known, ref_slli_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_slli_memory_protocol
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
theorem reference_srli_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20499) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_srli_v1066 s i commit known, ref_srli_v1074 s i commit known, ref_srli_v1082 s i commit known, ref_srli_v1090 s i commit known, ref_srli_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_srli_v1333 s i commit known, ref_srli_v1339 s i commit known, ref_srli_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_srli_v1333 s i commit known, ref_srli_v1339 s i commit known, ref_srli_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_srli_memory_protocol
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
theorem reference_srai_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762323) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_srai_v1066 s i commit known, ref_srai_v1074 s i commit known, ref_srai_v1082 s i commit known, ref_srai_v1090 s i commit known, ref_srai_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_srai_v1333 s i commit known, ref_srai_v1339 s i commit known, ref_srai_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_srai_v1333 s i commit known, ref_srai_v1339 s i commit known, ref_srai_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_srai_memory_protocol
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
theorem reference_add_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 51) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_add_v1066 s i commit known, ref_add_v1074 s i commit known, ref_add_v1082 s i commit known, ref_add_v1090 s i commit known, ref_add_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_add_v1333 s i commit known, ref_add_v1339 s i commit known, ref_add_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_add_v1333 s i commit known, ref_add_v1339 s i commit known, ref_add_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_add_memory_protocol
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
theorem reference_sub_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073741875) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sub_v1066 s i commit known, ref_sub_v1074 s i commit known, ref_sub_v1082 s i commit known, ref_sub_v1090 s i commit known, ref_sub_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sub_v1333 s i commit known, ref_sub_v1339 s i commit known, ref_sub_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sub_v1333 s i commit known, ref_sub_v1339 s i commit known, ref_sub_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_sub_memory_protocol
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
theorem reference_sll_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 4147) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sll_v1066 s i commit known, ref_sll_v1074 s i commit known, ref_sll_v1082 s i commit known, ref_sll_v1090 s i commit known, ref_sll_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sll_v1333 s i commit known, ref_sll_v1339 s i commit known, ref_sll_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sll_v1333 s i commit known, ref_sll_v1339 s i commit known, ref_sll_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_sll_memory_protocol
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
theorem reference_slt_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 8243) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_slt_v1066 s i commit known, ref_slt_v1074 s i commit known, ref_slt_v1082 s i commit known, ref_slt_v1090 s i commit known, ref_slt_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_slt_v1333 s i commit known, ref_slt_v1339 s i commit known, ref_slt_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_slt_v1333 s i commit known, ref_slt_v1339 s i commit known, ref_slt_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_slt_memory_protocol
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
theorem reference_sltu_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 12339) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sltu_v1066 s i commit known, ref_sltu_v1074 s i commit known, ref_sltu_v1082 s i commit known, ref_sltu_v1090 s i commit known, ref_sltu_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sltu_v1333 s i commit known, ref_sltu_v1339 s i commit known, ref_sltu_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sltu_v1333 s i commit known, ref_sltu_v1339 s i commit known, ref_sltu_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_sltu_memory_protocol
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
theorem reference_xor_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 16435) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_xor_v1066 s i commit known, ref_xor_v1074 s i commit known, ref_xor_v1082 s i commit known, ref_xor_v1090 s i commit known, ref_xor_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_xor_v1333 s i commit known, ref_xor_v1339 s i commit known, ref_xor_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_xor_v1333 s i commit known, ref_xor_v1339 s i commit known, ref_xor_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_xor_memory_protocol
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
theorem reference_srl_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 20531) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_srl_v1066 s i commit known, ref_srl_v1074 s i commit known, ref_srl_v1082 s i commit known, ref_srl_v1090 s i commit known, ref_srl_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_srl_v1333 s i commit known, ref_srl_v1339 s i commit known, ref_srl_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_srl_v1333 s i commit known, ref_srl_v1339 s i commit known, ref_srl_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_srl_memory_protocol
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
theorem reference_sra_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 1073762355) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sra_v1066 s i commit known, ref_sra_v1074 s i commit known, ref_sra_v1082 s i commit known, ref_sra_v1090 s i commit known, ref_sra_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sra_v1333 s i commit known, ref_sra_v1339 s i commit known, ref_sra_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_sra_v1333 s i commit known, ref_sra_v1339 s i commit known, ref_sra_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_sra_memory_protocol
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
theorem reference_or_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 24627) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_or_v1066 s i commit known, ref_or_v1074 s i commit known, ref_or_v1082 s i commit known, ref_or_v1090 s i commit known, ref_or_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_or_v1333 s i commit known, ref_or_v1339 s i commit known, ref_or_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_or_v1333 s i commit known, ref_or_v1339 s i commit known, ref_or_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_or_memory_protocol
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
theorem reference_and_memory_protocol (s : State) (i : Inputs)
    (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 4261441663 = 28723) :
    v9166 s i = 0 ∧ v9190 s i = 0 ∧ v9203 s i = 0 ∧ v9263 s i = 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, v9158, v9160, v9161, v9163, v9164, v9165, v9166, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_and_v1066 s i commit known, ref_and_v1074 s i commit known, ref_and_v1082 s i commit known, ref_and_v1090 s i commit known, ref_and_v1098 s i commit known, v1941, v9180, v9182, v9184, v9185, v9187, v9188, v9189, v9190, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_and_v1333 s i commit known, ref_and_v1339 s i commit known, ref_and_v1345 s i commit known, v9198, v9200, v9201, v9202, v9203, commit, BitVec.reduceEq, if_true, if_false]
  · simp only [ref_and_v1333 s i commit known, ref_and_v1339 s i commit known, ref_and_v1345 s i commit known, v1941, v9256, v9258, v9260, v9261, v9262, v9263, commit, BitVec.reduceEq, if_true, if_false]
#print axioms reference_and_memory_protocol
end RiscvMiniProofs
