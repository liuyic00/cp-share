import Proofs.MulDivSignedRequest

namespace HierarchicalMulDiv
open DesignnMulDiv.nMulDiv

attribute [local simp] v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v105 v106 v107 v108 v109 v110 v111 v112 v113 v114 v115 v116 v117 v118 v119 v120 v121 v122 v123 v124 v125 v126 v127 v128 v129 v130 v131 v132 v133 v134 v135 v136 v137 v138 v139 v140 v141 v142 v143 v144 v145 v146 v147 v148 v149 v150 v151

/-- One multiplier iteration, including the sign digit inserted before the
    final iteration. The packed state keeps the sign digit separate. -/
def multiplyAdvance (bits : BitVec 130) (d : BitVec 65)
    (count : BitVec 7) (negative : BitVec 1) : BitVec 130 :=
  let digit := BitVec.replicate 65 (BitVec.extractLsb' 64 1 bits) ++ BitVec.extractLsb' 0 1 bits
  let multiplicand := BitVec.extractLsb' 64 1 d ++ d
  let accumulator := BitVec.extractLsb' 129 1 bits ++ BitVec.extractLsb' 65 65 bits
  let product := digit * multiplicand + accumulator
  let sign := (if count = 62#7 then 1#1 else 0#1) &&& negative
  ((BitVec.extractLsb' 1 65 product ++ sign) ++ BitVec.extractLsb' 0 1 product) ++
    BitVec.extractLsb' 1 63 bits

theorem multiplication_edge (s : State) (i : Inputs) (multiplying : s.r0_nstate = 2) :
    (step s i).r8_nremainder = multiplyAdvance s.r8_nremainder s.r7_ndivisor
      s.r3_ncount s.r4_nneg_5Fout := by
  simp [step, eval_eq_spec, evalSpec, multiplying, multiplyAdvance]

/-- Multiplication consumes one digit per edge, retaining its operand and
    metadata until the last digit selects the final response half. -/
theorem multiplication_control (s : State) (i : Inputs)
    (multiplying : s.r0_nstate = 2) (reset : i.nreset = 0) (alive : i.nio_5Fkill = 0) :
    (step s i).r0_nstate = (if s.r3_ncount = 63#7 then 6#3 else 2#3) ∧
    (step s i).r3_ncount = s.r3_ncount + 1#7 ∧
    (step s i).r7_ndivisor = s.r7_ndivisor ∧
    (step s i).r4_nneg_5Fout = s.r4_nneg_5Fout ∧ metadata (step s i) = metadata s := by
  simp [step, eval_eq_spec, evalSpec, multiplying, reset, alive, metadata]
  bv_decide

#print axioms multiplication_edge
#print axioms multiplication_control
end HierarchicalMulDiv
