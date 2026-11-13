import Proofs.MulDivMultiplyExecution

namespace HierarchicalMulDiv
open DesignnMulDiv.nMulDiv

attribute [local simp] v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v105 v106 v107 v108 v109 v110 v111 v112 v113 v114 v115 v116 v117 v118 v119 v120 v121 v122 v123 v124 v125 v126 v127 v128 v129 v130 v131 v132 v133 v134 v135 v136 v137 v138 v139 v140 v141 v142 v143 v144 v145 v146 v147 v148 v149 v150 v151

/-- High-product requests capture signedness independently for the two
    operands. All three variants execute the same 64-digit datapath. -/
theorem capture_high_product (s : State) (i : Inputs)
    (idle : s.r0_nstate = 0) (valid : i.nio_5Freq_5Fvalid = 1)
    (reset : i.nreset = 0) (full : i.nio_5Freq_5Fbits_5Fdw = 1)
    (operation : i.nio_5Freq_5Fbits_5Ffn = 1#4 ∨ i.nio_5Freq_5Fbits_5Ffn = 2#4 ∨ i.nio_5Freq_5Fbits_5Ffn = 3#4) :
    (step s i).r0_nstate = 2 ∧ (step s i).r3_ncount = 0#7 ∧
    (step s i).r7_ndivisor =
      (if i.nio_5Freq_5Fbits_5Ffn = 1#4 then operandSign i.nio_5Freq_5Fbits_5Fin2 else 0#1) ++ i.nio_5Freq_5Fbits_5Fin2 ∧
    (step s i).r8_nremainder = 0#66 ++ i.nio_5Freq_5Fbits_5Fin1 ∧
    (step s i).r4_nneg_5Fout =
      (if i.nio_5Freq_5Fbits_5Ffn = 3#4 then 0#1 else operandSign i.nio_5Freq_5Fbits_5Fin1) ∧
    (step s i).r6_nresHi = 0#1 ∧
    metadata (step s i) = (1#1, i.nio_5Freq_5Fbits_5Ftag, 1#1) := by
  rcases operation with operation | operation | operation
  all_goals simp [step, eval_eq_spec, evalSpec, idle, valid, reset, full, operation, operandSign, metadata]
  all_goals bv_decide

/-- Low-product requests share the signed datapath. Word multiplication starts
    at count 32 and uses sign-extended low words, leaving 32 iterations. -/
theorem capture_low_product (s : State) (i : Inputs)
    (idle : s.r0_nstate = 0) (valid : i.nio_5Freq_5Fvalid = 1)
    (reset : i.nreset = 0) (operation : i.nio_5Freq_5Fbits_5Ffn = 0#4) :
    let a := signedA i
    let b := signedB i
    (step s i).r0_nstate = 2 ∧
    (step s i).r3_ncount = (if i.nio_5Freq_5Fbits_5Fdw = 1 then 0#7 else 32#7) ∧
    (step s i).r7_ndivisor = operandSign b ++ b ∧
    (step s i).r8_nremainder = 0#66 ++ a ∧
    (step s i).r4_nneg_5Fout = operandSign a ^^^ operandSign b ∧
    (step s i).r6_nresHi = 0#1 ∧
    metadata (step s i) = (i.nio_5Freq_5Fbits_5Fdw, i.nio_5Freq_5Fbits_5Ftag, 0#1) := by
  simp [step, eval_eq_spec, evalSpec, idle, valid, reset, operation,
    signedA, signedB, signedOperand, operandSign, metadata]
  bv_decide

#print axioms capture_low_product
#print axioms capture_high_product
end HierarchicalMulDiv
