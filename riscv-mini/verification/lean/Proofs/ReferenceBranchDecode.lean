import Proofs.ReferenceReads
import Proofs.BranchImmediate
import Proofs.MaskFacts
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedSimpArgs false
set_option maxRecDepth 4096
private theorem reference_commit_instruction (s : State) (i : Inputs) (commit : v964 s i = 1) :
    v977 s i = s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by simp [v977, v975, v974, v973, commit]
private theorem ref_beq_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_beq_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
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
private theorem ref_beq_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1379 s i = 0 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 4195 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_v1386 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v1386 s i = 1 := by
  change (if (99 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_beq_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_beq_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 99 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_beq_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_beq_v1005 s i commit known, ref_beq_v1013 s i commit known, ref_beq_v1021 s i commit known, ref_beq_v1029 s i commit known, ref_beq_v1037 s i commit known, ref_beq_v1046 s i commit known, ref_beq_v1052 s i commit known, ref_beq_v1058 s i commit known, ref_beq_v1066 s i commit known, ref_beq_v1074 s i commit known, ref_beq_v1082 s i commit known, ref_beq_v1090 s i commit known, ref_beq_v1098 s i commit known, ref_beq_v1333 s i commit known, ref_beq_v1339 s i commit known, ref_beq_v1345 s i commit known, ref_beq_v1351 s i commit known, ref_beq_v1358 s i commit known, ref_beq_v1365 s i commit known, ref_beq_v1372 s i commit known, ref_beq_v1379 s i commit known, ref_beq_v1386 s i commit known, v1387, v1388, v1573, v1574, v1615, v1616, v1617, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_beq_v980 s i commit known, ref_beq_v989 s i commit known, ref_beq_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_beq_rs2 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) :
    v1427 s i = BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_beq_v1005 s i commit known, ref_beq_v1013 s i commit known, ref_beq_v1021 s i commit known, ref_beq_v1029 s i commit known, ref_beq_v1037 s i commit known, ref_beq_v1333 s i commit known, ref_beq_v1339 s i commit known, ref_beq_v1345 s i commit known, ref_beq_v1351 s i commit known, ref_beq_v1358 s i commit known, ref_beq_v1365 s i commit known, ref_beq_v1372 s i commit known, ref_beq_v1379 s i commit known, ref_beq_v1386 s i commit known, v1387, v1388, v1389, v1410, v1411, v1412, v1413, v1414, v1415, v1416, v1417, v1418, v1419, v1420, v1421, v1422, v1423, v1424, v1425, v1426, v1427, commit, reference_commit_instruction s i commit, ref_beq_v980 s i commit known, ref_beq_v989 s i commit known, ref_beq_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 20+j < 25 by omega, show 20+j < 31 by omega, show 20+j < 32 by omega]
theorem reference_beq_immediate (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) : v2092 s i = immediateB s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_beq_v1046 s i commit known, ref_beq_v1052 s i commit known, ref_beq_v1058 s i commit known, ref_beq_v1066 s i commit known, ref_beq_v1074 s i commit known, ref_beq_v1082 s i commit known, ref_beq_v1090 s i commit known, ref_beq_v1098 s i commit known, ref_beq_v1333 s i commit known, ref_beq_v1339 s i commit known, ref_beq_v1345 s i commit known, ref_beq_v1351 s i commit known, ref_beq_v1358 s i commit known, ref_beq_v1365 s i commit known, ref_beq_v1372 s i commit known, ref_beq_v1379 s i commit known, ref_beq_v1386 s i commit known, v1387, v1388, v1573, v1893, v1894, v1895, v1896, v1897, v1898, v1899, v1900, v1921, v1922, v1923, v1924, v1927, v1928, v1929, v1930, v1931, v1932, v1933, v1940, v1942, v1943, v1944, v1945, v1946, v1947, v1948, v1955, v1956, v1957, v1958, v1959, v1960, v1961, v1962, v1966, v1967, v1998, v1999, v2000, v2001, v2002, v2003, v2004, v2075, v2076, v2077, v2078, v2079, v2080, v2081, v2082, v2083, v2084, v2085, v2086, v2087, v2088, v2089, v2090, v2091, v2092, v4, commit, reference_commit_instruction s i commit, BitVec.reduceEq, if_true, if_false]
  rw [branch_sign_conditional]
  simp [immediateB, branchBits, extract_prefix]
theorem reference_beq_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_beq_rs1 s i commit known]
theorem reference_beq_operand2 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 99) :
    v1539 s i = referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port2 s i zero, reference_beq_rs2 s i commit known]
private theorem ref_bne_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_bne_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
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
private theorem ref_bne_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1372 s i = 0 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 16483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_v1379 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v1379 s i = 1 := by
  change (if (4195 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_bne_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bne_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 4195 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_bne_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_bne_v1005 s i commit known, ref_bne_v1013 s i commit known, ref_bne_v1021 s i commit known, ref_bne_v1029 s i commit known, ref_bne_v1037 s i commit known, ref_bne_v1046 s i commit known, ref_bne_v1052 s i commit known, ref_bne_v1058 s i commit known, ref_bne_v1066 s i commit known, ref_bne_v1074 s i commit known, ref_bne_v1082 s i commit known, ref_bne_v1090 s i commit known, ref_bne_v1098 s i commit known, ref_bne_v1333 s i commit known, ref_bne_v1339 s i commit known, ref_bne_v1345 s i commit known, ref_bne_v1351 s i commit known, ref_bne_v1358 s i commit known, ref_bne_v1365 s i commit known, ref_bne_v1372 s i commit known, ref_bne_v1379 s i commit known, v1380, v1381, v1571, v1572, v1616, v1617, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_bne_v980 s i commit known, ref_bne_v989 s i commit known, ref_bne_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_bne_rs2 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) :
    v1427 s i = BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_bne_v1005 s i commit known, ref_bne_v1013 s i commit known, ref_bne_v1021 s i commit known, ref_bne_v1029 s i commit known, ref_bne_v1037 s i commit known, ref_bne_v1333 s i commit known, ref_bne_v1339 s i commit known, ref_bne_v1345 s i commit known, ref_bne_v1351 s i commit known, ref_bne_v1358 s i commit known, ref_bne_v1365 s i commit known, ref_bne_v1372 s i commit known, ref_bne_v1379 s i commit known, v1380, v1381, v1382, v1411, v1412, v1413, v1414, v1415, v1416, v1417, v1418, v1419, v1420, v1421, v1422, v1423, v1424, v1425, v1426, v1427, commit, reference_commit_instruction s i commit, ref_bne_v980 s i commit known, ref_bne_v989 s i commit known, ref_bne_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 20+j < 25 by omega, show 20+j < 31 by omega, show 20+j < 32 by omega]
theorem reference_bne_immediate (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) : v2092 s i = immediateB s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_bne_v1046 s i commit known, ref_bne_v1052 s i commit known, ref_bne_v1058 s i commit known, ref_bne_v1066 s i commit known, ref_bne_v1074 s i commit known, ref_bne_v1082 s i commit known, ref_bne_v1090 s i commit known, ref_bne_v1098 s i commit known, ref_bne_v1333 s i commit known, ref_bne_v1339 s i commit known, ref_bne_v1345 s i commit known, ref_bne_v1351 s i commit known, ref_bne_v1358 s i commit known, ref_bne_v1365 s i commit known, ref_bne_v1372 s i commit known, ref_bne_v1379 s i commit known, v1380, v1381, v1571, v1892, v1895, v1896, v1897, v1898, v1899, v1900, v1917, v1918, v1919, v1920, v1928, v1929, v1930, v1931, v1932, v1933, v1939, v1943, v1944, v1945, v1946, v1947, v1948, v1954, v1957, v1958, v1959, v1960, v1961, v1962, v1966, v1967, v1991, v1992, v1993, v1994, v1995, v1996, v1997, v2076, v2077, v2078, v2079, v2080, v2081, v2082, v2083, v2084, v2085, v2086, v2087, v2088, v2089, v2090, v2091, v2092, v4, commit, reference_commit_instruction s i commit, BitVec.reduceEq, if_true, if_false]
  rw [branch_sign_conditional]
  simp [immediateB, branchBits, extract_prefix]
theorem reference_bne_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_bne_rs1 s i commit known]
theorem reference_bne_operand2 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 4195) :
    v1539 s i = referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port2 s i zero, reference_bne_rs2 s i commit known]
private theorem ref_blt_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_blt_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
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
private theorem ref_blt_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1365 s i = 0 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 24675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_v1372 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v1372 s i = 1 := by
  change (if (16483 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_blt_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_blt_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 16483 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_blt_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_blt_v1005 s i commit known, ref_blt_v1013 s i commit known, ref_blt_v1021 s i commit known, ref_blt_v1029 s i commit known, ref_blt_v1037 s i commit known, ref_blt_v1046 s i commit known, ref_blt_v1052 s i commit known, ref_blt_v1058 s i commit known, ref_blt_v1066 s i commit known, ref_blt_v1074 s i commit known, ref_blt_v1082 s i commit known, ref_blt_v1090 s i commit known, ref_blt_v1098 s i commit known, ref_blt_v1333 s i commit known, ref_blt_v1339 s i commit known, ref_blt_v1345 s i commit known, ref_blt_v1351 s i commit known, ref_blt_v1358 s i commit known, ref_blt_v1365 s i commit known, ref_blt_v1372 s i commit known, v1373, v1374, v1569, v1570, v1617, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_blt_v980 s i commit known, ref_blt_v989 s i commit known, ref_blt_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_blt_rs2 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) :
    v1427 s i = BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_blt_v1005 s i commit known, ref_blt_v1013 s i commit known, ref_blt_v1021 s i commit known, ref_blt_v1029 s i commit known, ref_blt_v1037 s i commit known, ref_blt_v1333 s i commit known, ref_blt_v1339 s i commit known, ref_blt_v1345 s i commit known, ref_blt_v1351 s i commit known, ref_blt_v1358 s i commit known, ref_blt_v1365 s i commit known, ref_blt_v1372 s i commit known, v1373, v1374, v1375, v1412, v1413, v1414, v1415, v1416, v1417, v1418, v1419, v1420, v1421, v1422, v1423, v1424, v1425, v1426, v1427, commit, reference_commit_instruction s i commit, ref_blt_v980 s i commit known, ref_blt_v989 s i commit known, ref_blt_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 20+j < 25 by omega, show 20+j < 31 by omega, show 20+j < 32 by omega]
theorem reference_blt_immediate (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) : v2092 s i = immediateB s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_blt_v1046 s i commit known, ref_blt_v1052 s i commit known, ref_blt_v1058 s i commit known, ref_blt_v1066 s i commit known, ref_blt_v1074 s i commit known, ref_blt_v1082 s i commit known, ref_blt_v1090 s i commit known, ref_blt_v1098 s i commit known, ref_blt_v1333 s i commit known, ref_blt_v1339 s i commit known, ref_blt_v1345 s i commit known, ref_blt_v1351 s i commit known, ref_blt_v1358 s i commit known, ref_blt_v1365 s i commit known, ref_blt_v1372 s i commit known, v1373, v1374, v1569, v1891, v1896, v1897, v1898, v1899, v1900, v1913, v1914, v1915, v1916, v1929, v1930, v1931, v1932, v1933, v1938, v1944, v1945, v1946, v1947, v1948, v1953, v1958, v1959, v1960, v1961, v1962, v1966, v1967, v1984, v1985, v1986, v1987, v1988, v1989, v1990, v2077, v2078, v2079, v2080, v2081, v2082, v2083, v2084, v2085, v2086, v2087, v2088, v2089, v2090, v2091, v2092, v4, commit, reference_commit_instruction s i commit, BitVec.reduceEq, if_true, if_false]
  rw [branch_sign_conditional]
  simp [immediateB, branchBits, extract_prefix]
theorem reference_blt_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_blt_rs1 s i commit known]
theorem reference_blt_operand2 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 16483) :
    v1539 s i = referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port2 s i zero, reference_blt_rs2 s i commit known]
private theorem ref_bge_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_bge_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
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
private theorem ref_bge_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v1358 s i = 1 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_bge_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bge_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 20579 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_bge_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_bge_v1005 s i commit known, ref_bge_v1013 s i commit known, ref_bge_v1021 s i commit known, ref_bge_v1029 s i commit known, ref_bge_v1037 s i commit known, ref_bge_v1046 s i commit known, ref_bge_v1052 s i commit known, ref_bge_v1058 s i commit known, ref_bge_v1066 s i commit known, ref_bge_v1074 s i commit known, ref_bge_v1082 s i commit known, ref_bge_v1090 s i commit known, ref_bge_v1098 s i commit known, ref_bge_v1333 s i commit known, ref_bge_v1339 s i commit known, ref_bge_v1345 s i commit known, ref_bge_v1351 s i commit known, ref_bge_v1358 s i commit known, v1359, v1360, v1565, v1566, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_bge_v980 s i commit known, ref_bge_v989 s i commit known, ref_bge_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_bge_rs2 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) :
    v1427 s i = BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_bge_v1005 s i commit known, ref_bge_v1013 s i commit known, ref_bge_v1021 s i commit known, ref_bge_v1029 s i commit known, ref_bge_v1037 s i commit known, ref_bge_v1333 s i commit known, ref_bge_v1339 s i commit known, ref_bge_v1345 s i commit known, ref_bge_v1351 s i commit known, ref_bge_v1358 s i commit known, v1359, v1360, v1361, v1414, v1415, v1416, v1417, v1418, v1419, v1420, v1421, v1422, v1423, v1424, v1425, v1426, v1427, commit, reference_commit_instruction s i commit, ref_bge_v980 s i commit known, ref_bge_v989 s i commit known, ref_bge_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 20+j < 25 by omega, show 20+j < 31 by omega, show 20+j < 32 by omega]
theorem reference_bge_immediate (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) : v2092 s i = immediateB s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_bge_v1046 s i commit known, ref_bge_v1052 s i commit known, ref_bge_v1058 s i commit known, ref_bge_v1066 s i commit known, ref_bge_v1074 s i commit known, ref_bge_v1082 s i commit known, ref_bge_v1090 s i commit known, ref_bge_v1098 s i commit known, ref_bge_v1333 s i commit known, ref_bge_v1339 s i commit known, ref_bge_v1345 s i commit known, ref_bge_v1351 s i commit known, ref_bge_v1358 s i commit known, v1359, v1360, v1565, v1889, v1898, v1899, v1900, v1905, v1906, v1907, v1908, v1931, v1932, v1933, v1936, v1946, v1947, v1948, v1951, v1960, v1961, v1962, v1966, v1967, v1970, v1971, v1972, v1973, v1974, v1975, v1976, v2079, v2080, v2081, v2082, v2083, v2084, v2085, v2086, v2087, v2088, v2089, v2090, v2091, v2092, v4, commit, reference_commit_instruction s i commit, BitVec.reduceEq, if_true, if_false]
  rw [branch_sign_conditional]
  simp [immediateB, branchBits, extract_prefix]
theorem reference_bge_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_bge_rs1 s i commit known]
theorem reference_bge_operand2 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 20579) :
    v1539 s i = referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port2 s i zero, reference_bge_rs2 s i commit known]
private theorem ref_bltu_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_bltu_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
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
private theorem ref_bltu_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1351 s i = 0 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 28771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_v1358 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1358 s i = 0 := by
  change (if (20579 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 20579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_v1365 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v1365 s i = 1 := by
  change (if (24675 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_bltu_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bltu_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 24675 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_bltu_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_bltu_v1005 s i commit known, ref_bltu_v1013 s i commit known, ref_bltu_v1021 s i commit known, ref_bltu_v1029 s i commit known, ref_bltu_v1037 s i commit known, ref_bltu_v1046 s i commit known, ref_bltu_v1052 s i commit known, ref_bltu_v1058 s i commit known, ref_bltu_v1066 s i commit known, ref_bltu_v1074 s i commit known, ref_bltu_v1082 s i commit known, ref_bltu_v1090 s i commit known, ref_bltu_v1098 s i commit known, ref_bltu_v1333 s i commit known, ref_bltu_v1339 s i commit known, ref_bltu_v1345 s i commit known, ref_bltu_v1351 s i commit known, ref_bltu_v1358 s i commit known, ref_bltu_v1365 s i commit known, v1366, v1367, v1567, v1568, v1618, v1619, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_bltu_v980 s i commit known, ref_bltu_v989 s i commit known, ref_bltu_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_bltu_rs2 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) :
    v1427 s i = BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_bltu_v1005 s i commit known, ref_bltu_v1013 s i commit known, ref_bltu_v1021 s i commit known, ref_bltu_v1029 s i commit known, ref_bltu_v1037 s i commit known, ref_bltu_v1333 s i commit known, ref_bltu_v1339 s i commit known, ref_bltu_v1345 s i commit known, ref_bltu_v1351 s i commit known, ref_bltu_v1358 s i commit known, ref_bltu_v1365 s i commit known, v1366, v1367, v1368, v1413, v1414, v1415, v1416, v1417, v1418, v1419, v1420, v1421, v1422, v1423, v1424, v1425, v1426, v1427, commit, reference_commit_instruction s i commit, ref_bltu_v980 s i commit known, ref_bltu_v989 s i commit known, ref_bltu_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 20+j < 25 by omega, show 20+j < 31 by omega, show 20+j < 32 by omega]
theorem reference_bltu_immediate (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) : v2092 s i = immediateB s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_bltu_v1046 s i commit known, ref_bltu_v1052 s i commit known, ref_bltu_v1058 s i commit known, ref_bltu_v1066 s i commit known, ref_bltu_v1074 s i commit known, ref_bltu_v1082 s i commit known, ref_bltu_v1090 s i commit known, ref_bltu_v1098 s i commit known, ref_bltu_v1333 s i commit known, ref_bltu_v1339 s i commit known, ref_bltu_v1345 s i commit known, ref_bltu_v1351 s i commit known, ref_bltu_v1358 s i commit known, ref_bltu_v1365 s i commit known, v1366, v1367, v1567, v1890, v1897, v1898, v1899, v1900, v1909, v1910, v1911, v1912, v1930, v1931, v1932, v1933, v1937, v1945, v1946, v1947, v1948, v1952, v1959, v1960, v1961, v1962, v1966, v1967, v1977, v1978, v1979, v1980, v1981, v1982, v1983, v2078, v2079, v2080, v2081, v2082, v2083, v2084, v2085, v2086, v2087, v2088, v2089, v2090, v2091, v2092, v4, commit, reference_commit_instruction s i commit, BitVec.reduceEq, if_true, if_false]
  rw [branch_sign_conditional]
  simp [immediateB, branchBits, extract_prefix]
theorem reference_bltu_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_bltu_rs1 s i commit known]
theorem reference_bltu_operand2 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 24675) :
    v1539 s i = referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port2 s i zero, reference_bltu_rs2 s i commit known]
private theorem ref_bgeu_v1005 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1005 s i = 0 := by
  change (if (33570867 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 4261441663 33570867 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_v1013 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1013 s i = 0 := by
  change (if (33566771 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 4261441663 33566771 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_v1021 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1021 s i = 0 := by
  change (if (33562675 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 4261441663 33562675 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_v1029 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1029 s i = 0 := by
  change (if (33558579 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 4261441663 33558579 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_v1037 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1037 s i = 0 := by
  change (if (33554483 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 4261441663 33554483 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_v1046 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1046 s i = 0 := by
  change (if (15 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 15 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_v1052 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1052 s i = 0 := by
  change (if (115 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 4294967295 115 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 115 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
private theorem ref_bgeu_v1058 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1058 s i = 0 := by
  change (if (1048691 : BitVec 32) = v977 s i then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 4294967295 1048691 known (by decide)
  have direct : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst ≠ 1048691 := by
    intro he; apply no; rw [he]; decide
  rw [if_neg (Ne.symm direct)]
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
private theorem ref_bgeu_v1351 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v1351 s i = 1 := by
  change (if (28771 : BitVec 32) = (v977 s i &&& 28799) then 1 else 0) = 1
  rw [reference_commit_instruction s i commit]
  have yes : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771 :=
    mask_refines s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 28799 known (by decide)
  rw [if_pos yes.symm]
private theorem ref_bgeu_v980 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v980 s i = 0 := by
  change (if (33583155 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 4261441663 33583155 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_v989 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v989 s i = 0 := by
  change (if (33579059 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 4261441663 33579059 known (by decide)
  rw [if_neg (Ne.symm no)]
private theorem ref_bgeu_v997 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v997 s i = 0 := by
  change (if (33574963 : BitVec 32) = (v977 s i &&& 4261441663) then 1 else 0) = 0
  rw [reference_commit_instruction s i commit]
  have no := mask_incompatible s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst 28799 28771 4261441663 33574963 known (by decide)
  rw [if_neg (Ne.symm no)]
theorem reference_bgeu_rs1 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) :
    v1640 s i = BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_bgeu_v1005 s i commit known, ref_bgeu_v1013 s i commit known, ref_bgeu_v1021 s i commit known, ref_bgeu_v1029 s i commit known, ref_bgeu_v1037 s i commit known, ref_bgeu_v1046 s i commit known, ref_bgeu_v1052 s i commit known, ref_bgeu_v1058 s i commit known, ref_bgeu_v1066 s i commit known, ref_bgeu_v1074 s i commit known, ref_bgeu_v1082 s i commit known, ref_bgeu_v1090 s i commit known, ref_bgeu_v1098 s i commit known, ref_bgeu_v1333 s i commit known, ref_bgeu_v1339 s i commit known, ref_bgeu_v1345 s i commit known, ref_bgeu_v1351 s i commit known, v1352, v1353, v1563, v1564, v1620, v1621, v1622, v1623, v1624, v1625, v1626, v1627, v1628, v1629, v1630, v1631, v1632, v1633, v1634, v1635, v1636, v1637, v1638, v1639, v1640, commit, reference_commit_instruction s i commit, ref_bgeu_v980 s i commit known, ref_bgeu_v989 s i commit known, ref_bgeu_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 15+j < 20 by omega, show 15+j < 21 by omega, show 15+j < 25 by omega, show 15+j < 31 by omega, show 15+j < 32 by omega]
theorem reference_bgeu_rs2 (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) :
    v1427 s i = BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_bgeu_v1005 s i commit known, ref_bgeu_v1013 s i commit known, ref_bgeu_v1021 s i commit known, ref_bgeu_v1029 s i commit known, ref_bgeu_v1037 s i commit known, ref_bgeu_v1333 s i commit known, ref_bgeu_v1339 s i commit known, ref_bgeu_v1345 s i commit known, ref_bgeu_v1351 s i commit known, v1352, v1353, v1354, v1415, v1416, v1417, v1418, v1419, v1420, v1421, v1422, v1423, v1424, v1425, v1426, v1427, commit, reference_commit_instruction s i commit, ref_bgeu_v980 s i commit known, ref_bgeu_v989 s i commit known, ref_bgeu_v997 s i commit known, if_true, if_false]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp only [BitVec.getLsbD_extractLsb']
  simp [hj, show 20+j < 25 by omega, show 20+j < 31 by omega, show 20+j < 32 by omega]
theorem reference_bgeu_immediate (s : State) (i : Inputs) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) : v2092 s i = immediateB s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst := by
  simp only [ref_bgeu_v1046 s i commit known, ref_bgeu_v1052 s i commit known, ref_bgeu_v1058 s i commit known, ref_bgeu_v1066 s i commit known, ref_bgeu_v1074 s i commit known, ref_bgeu_v1082 s i commit known, ref_bgeu_v1090 s i commit known, ref_bgeu_v1098 s i commit known, ref_bgeu_v1333 s i commit known, ref_bgeu_v1339 s i commit known, ref_bgeu_v1345 s i commit known, ref_bgeu_v1351 s i commit known, v1352, v1353, v1563, v1888, v1899, v1900, v1901, v1902, v1903, v1904, v1932, v1933, v1934, v1935, v1947, v1948, v1949, v1950, v1961, v1962, v1963, v1964, v1965, v1966, v1967, v1968, v1969, v2080, v2081, v2082, v2083, v2084, v2085, v2086, v2087, v2088, v2089, v2090, v2091, v2092, v4, commit, reference_commit_instruction s i commit, BitVec.reduceEq, if_true, if_false]
  rw [branch_sign_conditional]
  simp [immediateB, branchBits, extract_prefix]
theorem reference_bgeu_operand1 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) :
    v1721 s i = referenceRead s (BitVec.extractLsb' 15 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port1 s i zero, reference_bgeu_rs1 s i commit known]
theorem reference_bgeu_operand2 (s : State) (i : Inputs)
    (zero : ReferenceZero s) (commit : v964 s i = 1)
    (known : s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 28771) :
    v1539 s i = referenceRead s (BitVec.extractLsb' 20 5 s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst) := by
  rw [reference_mux_port2 s i zero, reference_bgeu_rs2 s i commit known]
end RiscvMiniProofs
