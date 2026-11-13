import Proofs.MulDivWordProduct
import Proofs.MulDivLowProduct

namespace HierarchicalMulDiv
open DesignnMulDiv.nMulDiv

attribute [local simp] v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v105 v106 v107 v108 v109 v110 v111 v112 v113 v114 v115 v116 v117 v118 v119 v120 v121 v122 v123 v124 v125 v126 v127 v128 v129 v130 v131 v132 v133 v134 v135 v136 v137 v138 v139 v140 v141 v142 v143 v144 v145 v146 v147 v148 v149 v150 v151 v152 v153 v154 v155 v156 v157 v158 v159 v160

theorem observe_word_product (s : State) (i : Inputs)
    (finished : s.r0_nstate = 6) (word : s.r1_nreq_5Fdw = 0) (low : s.r6_nresHi = 0) :
    (observe s i).nio_5Fresp_5Fvalid = 1 ∧
    (observe s i).nio_5Fresp_5Fbits_5Ftag = s.r2_nreq_5Ftag ∧
    (observe s i).nio_5Fresp_5Fbits_5Fdata = (BitVec.extractLsb' 32 32 s.r8_nremainder).signExtend 64 := by
  simp [observe, eval_eq_spec, evalSpec, finished, word, low]
  bv_decide

theorem word_product_core_result (s : State) (inputs : Nat → Inputs) (a : BitVec 64) (d : BitVec 65)
    (multiplying : s.r0_nstate = 2) (count : s.r3_ncount = 32#7)
    (divisor : s.r7_ndivisor = d) (initial : s.r8_nremainder = 0#66 ++ a)
    (word : s.r1_nreq_5Fdw = 0) (low : s.r5_nisHi = 0)
    (reset : ∀ t, t < 32 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 32 → (inputs t).nio_5Fkill = 0) :
    (observe (run s inputs 32) (inputs 32)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s inputs 32) (inputs 32)).nio_5Fresp_5Fbits_5Ftag = s.r2_nreq_5Ftag ∧
    (observe (run s inputs 32) (inputs 32)).nio_5Fresp_5Fbits_5Fdata =
      (a.setWidth 32 * d.setWidth 32).signExtend 64 := by
  have finish := multiplication_finishes s inputs multiplying 32 (by rw [count]; rfl) (by omega) reset alive
  have before := multiplication_prefix s inputs multiplying 32 (by rw [count]; rfl) reset alive 31 (by omega)
  have counter : (run s inputs 31).r3_ncount = 63#7 := BitVec.eq_of_toNat_eq before.2.1
  have previousMetadata := metadata_run s inputs 31 (by
    intro t bound
    have traceFacts := multiplication_prefix s inputs multiplying 32 (by rw [count]; rfl) reset alive t (by omega)
    rw [traceFacts.1]
    decide)
  have mode : (run s inputs 32).r6_nresHi = 0 :=
    (select_multiply_response _ _ before.1 counter).trans
      ((congrArg (fun m => m.2.2) previousMetadata).trans low)
  have width : (run s inputs 32).r1_nreq_5Fdw = 0 :=
    (congrArg (fun m => m.1) finish.2.2).trans word
  have output := observe_word_product (run s inputs 32) (inputs 32) finish.1 width mode
  refine ⟨output.1, output.2.1.trans (congrArg (fun m => m.2.1) finish.2.2), ?_⟩
  rw [output.2.2, finish.2.1, divisor, initial, word_packed_product]

theorem word_product_accepted (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (word : (inputs 0).nio_5Freq_5Fbits_5Fdw = 0)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 0#4)
    (reset : ∀ t, t < 33 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 33 → (inputs t).nio_5Fkill = 0) :
    (observe (run s inputs 33) (inputs 33)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s inputs 33) (inputs 33)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag ∧
    (observe (run s inputs 33) (inputs 33)).nio_5Fresp_5Fbits_5Fdata =
      ((inputs 0).nio_5Freq_5Fbits_5Fin1.setWidth 32 * (inputs 0).nio_5Freq_5Fbits_5Fin2.setWidth 32).signExtend 64 := by
  have captured := capture_low_product s (inputs 0) idle valid (reset 0 (by omega)) operation
  dsimp only [signedA, signedB, signedOperand] at captured
  simp only [word, BitVec.reduceEq, if_false] at captured
  have output := word_product_core_result (step s (inputs 0)) (fun t => inputs (1 + t)) _ _
    captured.1 captured.2.1 captured.2.2.1 captured.2.2.2.1
    (congrArg (fun m => m.1) captured.2.2.2.2.2.2)
    (congrArg (fun m => m.2.2) captured.2.2.2.2.2.2)
    (by intro t h; exact reset (1 + t) (by omega))
    (by intro t h; exact alive (1 + t) (by omega))
  have trajectory := run_offset s inputs 1 32
  change run s inputs 33 = run (step s (inputs 0)) (fun t => inputs (1 + t)) 32 at trajectory
  rw [trajectory]
  refine ⟨output.1, output.2.1.trans (congrArg (fun m => m.2.1) captured.2.2.2.2.2.2), ?_⟩
  rw [output.2.2]
  congr 2 <;> bv_decide

#print axioms word_product_accepted
#print axioms word_product_core_result
end HierarchicalMulDiv
