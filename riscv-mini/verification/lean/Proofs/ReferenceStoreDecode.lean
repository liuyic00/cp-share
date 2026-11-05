import Proofs.ReferenceReads
import Proofs.StoreImmediate
import Proofs.JumpImmediate
import Proofs.MaskFacts
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
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
theorem reference_sb_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sb_v1005 s i commit known, ref_sb_v1013 s i commit known, ref_sb_v1021 s i commit known, ref_sb_v1029 s i commit known, ref_sb_v1037 s i commit known, ref_sb_v1046 s i commit known, ref_sb_v1052 s i commit known, ref_sb_v1058 s i commit known, ref_sb_v1333 s i commit known, ref_sb_v1339 s i commit known, ref_sb_v1345 s i commit known, v1346, v1556, v1557, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_sb_v980 s i commit known, ref_sb_v989 s i commit known, ref_sb_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_sb_rs2 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) :
    v1427 s i = BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sb_v1005 s i commit known, ref_sb_v1013 s i commit known, ref_sb_v1021 s i commit known, ref_sb_v1029 s i commit known, ref_sb_v1037 s i commit known, ref_sb_v1333 s i commit known, ref_sb_v1339 s i commit known, ref_sb_v1345 s i commit known, v1346, v1347, v1416, v1417, v1418, v1419, v1420, v1421, v1422, v1423, v1424, v1425, v1426, v1427, commit, reference_commit_instruction s i commit, ref_sb_v980 s i commit known, ref_sb_v989 s i commit known, ref_sb_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 20+j < 25 by omega, show 20+j < 31 by omega, show 20+j < 32 by omega]
theorem reference_sb_immediate (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) : v2092 s i = immediateS s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sb_v1046 s i commit known, ref_sb_v1052 s i commit known, ref_sb_v1058 s i commit known, ref_sb_v1333 s i commit known, ref_sb_v1339 s i commit known, ref_sb_v1345 s i commit known, v1346, v1556, v1831, v1832, v1843, v1844, v1845, v1846, v1847, v1854, v1855, v1856, v1857, v1858, v1859, v1860, v1869, v1870, v1871, v1872, v2086, v2087, v2088, v2089, v2090, v2091, v2092, commit, reference_commit_instruction s i commit, BitVec.reduceEq, if_true, if_false]
  rw [reference_sign_extension]
  simp [immediateS, extract_prefix]
theorem reference_sb_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_sb_rs1 s i commit known]
theorem reference_sb_operand2 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 35) :
    v1539 s i = referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port2 s i zero, reference_sb_rs2 s i commit known]
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
theorem reference_sh_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sh_v1005 s i commit known, ref_sh_v1013 s i commit known, ref_sh_v1021 s i commit known, ref_sh_v1029 s i commit known, ref_sh_v1037 s i commit known, ref_sh_v1046 s i commit known, ref_sh_v1052 s i commit known, ref_sh_v1058 s i commit known, ref_sh_v1333 s i commit known, ref_sh_v1339 s i commit known, v1340, v1554, v1555, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_sh_v980 s i commit known, ref_sh_v989 s i commit known, ref_sh_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_sh_rs2 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) :
    v1427 s i = BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sh_v1005 s i commit known, ref_sh_v1013 s i commit known, ref_sh_v1021 s i commit known, ref_sh_v1029 s i commit known, ref_sh_v1037 s i commit known, ref_sh_v1333 s i commit known, ref_sh_v1339 s i commit known, v1340, v1341, v1417, v1418, v1419, v1420, v1421, v1422, v1423, v1424, v1425, v1426, v1427, commit, reference_commit_instruction s i commit, ref_sh_v980 s i commit known, ref_sh_v989 s i commit known, ref_sh_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 20+j < 25 by omega, show 20+j < 31 by omega, show 20+j < 32 by omega]
theorem reference_sh_immediate (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) : v2092 s i = immediateS s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sh_v1046 s i commit known, ref_sh_v1052 s i commit known, ref_sh_v1058 s i commit known, ref_sh_v1333 s i commit known, ref_sh_v1339 s i commit known, v1340, v1554, v1831, v1832, v1842, v1845, v1846, v1847, v1851, v1852, v1853, v1858, v1859, v1860, v1865, v1866, v1867, v1868, v2087, v2088, v2089, v2090, v2091, v2092, commit, reference_commit_instruction s i commit, BitVec.reduceEq, if_true, if_false]
  rw [reference_sign_extension]
  simp [immediateS, extract_prefix]
theorem reference_sh_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_sh_rs1 s i commit known]
theorem reference_sh_operand2 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4131) :
    v1539 s i = referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port2 s i zero, reference_sh_rs2 s i commit known]
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
theorem reference_sw_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sw_v1005 s i commit known, ref_sw_v1013 s i commit known, ref_sw_v1021 s i commit known, ref_sw_v1029 s i commit known, ref_sw_v1037 s i commit known, ref_sw_v1046 s i commit known, ref_sw_v1052 s i commit known, ref_sw_v1058 s i commit known, ref_sw_v1333 s i commit known, v1334, v1552, v1553, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_sw_v980 s i commit known, ref_sw_v989 s i commit known, ref_sw_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_sw_rs2 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) :
    v1427 s i = BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sw_v1005 s i commit known, ref_sw_v1013 s i commit known, ref_sw_v1021 s i commit known, ref_sw_v1029 s i commit known, ref_sw_v1037 s i commit known, ref_sw_v1333 s i commit known, v1334, v1335, v1418, v1419, v1420, v1421, v1422, v1423, v1424, v1425, v1426, v1427, commit, reference_commit_instruction s i commit, ref_sw_v980 s i commit known, ref_sw_v989 s i commit known, ref_sw_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 20+j < 25 by omega, show 20+j < 31 by omega, show 20+j < 32 by omega]
theorem reference_sw_immediate (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) : v2092 s i = immediateS s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_sw_v1046 s i commit known, ref_sw_v1052 s i commit known, ref_sw_v1058 s i commit known, ref_sw_v1333 s i commit known, v1334, v1552, v1831, v1832, v1841, v1846, v1847, v1848, v1849, v1850, v1859, v1860, v1861, v1862, v1863, v1864, v2088, v2089, v2090, v2091, v2092, commit, reference_commit_instruction s i commit, BitVec.reduceEq, if_true, if_false]
  rw [reference_sign_extension]
  simp [immediateS, extract_prefix]
theorem reference_sw_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_sw_rs1 s i commit known]
theorem reference_sw_operand2 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 8227) :
    v1539 s i = referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port2 s i zero, reference_sw_rs2 s i commit known]
end RiscvMiniProofs
