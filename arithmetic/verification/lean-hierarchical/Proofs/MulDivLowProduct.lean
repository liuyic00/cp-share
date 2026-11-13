import Proofs.MulDivSignedProductResponse

namespace HierarchicalMulDiv

theorem product_low_word (a : BitVec 64) (d : BitVec 65) (negative : BitVec 1) :
    (productBits a d negative).setWidth 64 = a * d.setWidth 64 := by
  unfold productBits
  rw [BitVec.ofInt_mul, BitVec.setWidth_mul _ _ (by omega)]
  have left : (BitVec.ofInt 128 ((a.toNat : Int) -
      (if negative = 1#1 then 2 ^ 64 else 0))).setWidth 64 = a := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth, BitVec.toNat_ofInt]
    have width := a.isLt
    split <;> omega
  have right : (BitVec.ofInt 128 d.toInt).setWidth 64 = d.setWidth 64 := by
    change (d.signExtend 128).setWidth 64 = d.setWidth 64
    bv_decide
  rw [left, right]

open DesignnMulDiv.nMulDiv

attribute [local simp] v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v105 v106 v107 v108 v109 v110 v111 v112 v113 v114 v115 v116 v117 v118 v119 v120 v121 v122 v123 v124 v125 v126 v127 v128 v129 v130 v131 v132 v133 v134 v135 v136 v137 v138 v139 v140 v141 v142 v143 v144 v145 v146 v147 v148 v149 v150 v151 v152 v153 v154 v155 v156 v157 v158 v159 v160

theorem observe_low_product (s : State) (i : Inputs)
    (finished : s.r0_nstate = 6) (full : s.r1_nreq_5Fdw = 1) (low : s.r6_nresHi = 0) :
    (observe s i).nio_5Fresp_5Fvalid = 1 ∧
    (observe s i).nio_5Fresp_5Fbits_5Ftag = s.r2_nreq_5Ftag ∧
    (observe s i).nio_5Fresp_5Fbits_5Fdata = BitVec.extractLsb' 0 64 s.r8_nremainder := by
  simp [observe, eval_eq_spec, evalSpec, finished, full, low]
  bv_decide

theorem low_product_core_result (s : State) (inputs : Nat → Inputs) (a : BitVec 64) (d : BitVec 65)
    (multiplying : s.r0_nstate = 2) (count : s.r3_ncount = 0#7)
    (divisor : s.r7_ndivisor = d) (initial : s.r8_nremainder = 0#66 ++ a)
    (full : s.r1_nreq_5Fdw = 1) (low : s.r5_nisHi = 0)
    (reset : ∀ t, t < 64 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 64 → (inputs t).nio_5Fkill = 0) :
    (observe (run s inputs 64) (inputs 64)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s inputs 64) (inputs 64)).nio_5Fresp_5Fbits_5Ftag = s.r2_nreq_5Ftag ∧
    (observe (run s inputs 64) (inputs 64)).nio_5Fresp_5Fbits_5Fdata =
      a * d.setWidth 64 := by
  have result := product_state s inputs a d multiplying count divisor initial reset alive
  have before := multiplication_prefix s inputs multiplying 0 (by rw [count]; rfl) reset alive 63 (by omega)
  have counter : (run s inputs 63).r3_ncount = 63#7 := BitVec.eq_of_toNat_eq before.2.1
  have previousMetadata := metadata_run s inputs 63 (by
    intro t bound
    have traceFacts := multiplication_prefix s inputs multiplying 0 (by rw [count]; rfl) reset alive t (by omega)
    rw [traceFacts.1]
    decide)
  have mode : (run s inputs 64).r6_nresHi = 0 :=
    (select_multiply_response _ _ before.1 counter).trans
      ((congrArg (fun m => m.2.2) previousMetadata).trans low)
  have width : (run s inputs 64).r1_nreq_5Fdw = 1 :=
    (congrArg (fun m => m.1) result.2.2).trans full
  have output := observe_low_product (run s inputs 64) (inputs 64) result.1 width mode
  refine ⟨output.1, output.2.1.trans (congrArg (fun m => m.2.1) result.2.2), ?_⟩
  rw [output.2.2]
  have slice : BitVec.extractLsb' 0 64 (run s inputs 64).r8_nremainder =
      ((unpackMultiply (run s inputs 64).r8_nremainder).setWidth 128).setWidth 64 := by
    unfold unpackMultiply
    bv_decide
  rw [slice, result.2.1, product_low_word]

/-- A full-width MUL request returns the mathematical product modulo 2^64
    after its acceptance edge and 64 computation edges. -/
theorem low_product_accepted (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (full : (inputs 0).nio_5Freq_5Fbits_5Fdw = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 0#4)
    (reset : ∀ t, t < 65 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 65 → (inputs t).nio_5Fkill = 0) :
    (observe (run s inputs 65) (inputs 65)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s inputs 65) (inputs 65)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag ∧
    (observe (run s inputs 65) (inputs 65)).nio_5Fresp_5Fbits_5Fdata =
      (inputs 0).nio_5Freq_5Fbits_5Fin1 * (inputs 0).nio_5Freq_5Fbits_5Fin2 := by
  have captured := capture_low_product s (inputs 0) idle valid (reset 0 (by omega)) operation
  dsimp only [signedA, signedB, signedOperand] at captured
  simp only [full, if_pos] at captured
  have output := low_product_core_result (step s (inputs 0)) (fun t => inputs (1 + t)) _ _
    captured.1 captured.2.1 captured.2.2.1 captured.2.2.2.1
    (congrArg (fun m => m.1) captured.2.2.2.2.2.2)
    (congrArg (fun m => m.2.2) captured.2.2.2.2.2.2)
    (by intro t h; exact reset (1 + t) (by omega))
    (by intro t h; exact alive (1 + t) (by omega))
  have trajectory := run_offset s inputs 1 64
  change run s inputs 65 = run (step s (inputs 0)) (fun t => inputs (1 + t)) 64 at trajectory
  rw [trajectory]
  refine ⟨output.1, output.2.1.trans (congrArg (fun m => m.2.1) captured.2.2.2.2.2.2), ?_⟩
  rw [output.2.2]
  congr 1
  bv_decide

#print axioms low_product_accepted
#print axioms low_product_core_result
#print axioms product_low_word
end HierarchicalMulDiv
