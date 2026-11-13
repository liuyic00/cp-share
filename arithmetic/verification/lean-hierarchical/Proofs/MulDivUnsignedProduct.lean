import Proofs.MulDivMultiplyValue

namespace HierarchicalMulDiv
open DesignnMulDiv.nMulDiv

attribute [local simp] v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v105 v106 v107 v108 v109 v110 v111 v112 v113 v114 v115 v116 v117 v118 v119 v120 v121 v122 v123 v124 v125 v126 v127 v128 v129 v130 v131 v132 v133 v134 v135 v136 v137 v138 v139 v140 v141 v142 v143 v144 v145 v146 v147 v148 v149 v150 v151 v152 v153 v154 v155 v156 v157 v158 v159 v160

/-- The actual multiplier state reaches the exact unsigned product after the
    64 computation edges, with the response metadata preserved. -/
theorem unsigned_product_state (s : State) (inputs : Nat → Inputs) (a d : BitVec 64)
    (multiplying : s.r0_nstate = 2) (count : s.r3_ncount = 0#7)
    (divisor : s.r7_ndivisor = 0#1 ++ d) (initial : s.r8_nremainder = 0#66 ++ a)
    (sign : s.r4_nneg_5Fout = 0#1)
    (reset : ∀ t, t < 64 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 64 → (inputs t).nio_5Fkill = 0) :
    (run s inputs 64).r0_nstate = 6 ∧
    (unpackMultiply (run s inputs 64).r8_nremainder).toNat = a.toNat * d.toNat ∧
    metadata (run s inputs 64) = metadata s := by
  have finish := multiplication_finishes s inputs multiplying 0
    (by rw [count]; rfl) (by omega) reset alive
  refine ⟨finish.1, ?_, finish.2.2⟩
  rw [finish.2.1, divisor, initial, sign]
  exact unsigned_packed_product a d

/-- The mathematical high half is precisely the hardware high-result slice. -/
theorem unpack_high (bits : BitVec 130) :
    (BitVec.extractLsb' 65 64 bits).toNat = (unpackMultiply bits).toNat / 2 ^ 64 % 2 ^ 64 := by
  have slices : BitVec.extractLsb' 65 64 bits = BitVec.extractLsb' 64 64 (unpackMultiply bits) := by
    unfold unpackMultiply
    bv_decide
  rw [slices]
  simp [Nat.shiftRight_eq_div_pow]

theorem select_multiply_response (s : State) (i : Inputs)
    (multiplying : s.r0_nstate = 2) (last : s.r3_ncount = 63#7) :
    (step s i).r6_nresHi = s.r5_nisHi := by
  simp [step, eval_eq_spec, evalSpec, multiplying, last]
  bv_decide

theorem observe_high_product (s : State) (i : Inputs)
    (finished : s.r0_nstate = 6) (full : s.r1_nreq_5Fdw = 1) (high : s.r6_nresHi = 1) :
    (observe s i).nio_5Fresp_5Fvalid = 1 ∧
    (observe s i).nio_5Fresp_5Fbits_5Ftag = s.r2_nreq_5Ftag ∧
    (observe s i).nio_5Fresp_5Fbits_5Fdata = BitVec.extractLsb' 65 64 s.r8_nremainder := by
  simp [observe, eval_eq_spec, evalSpec, finished, full, high]
  bv_decide

/-- The complete unsigned high-product computation emits the mathematical
    upper word, with valid and tag derived from the actual response state. -/
theorem unsigned_high_core_result (s : State) (inputs : Nat → Inputs) (a d : BitVec 64)
    (multiplying : s.r0_nstate = 2) (count : s.r3_ncount = 0#7)
    (divisor : s.r7_ndivisor = 0#1 ++ d) (initial : s.r8_nremainder = 0#66 ++ a)
    (sign : s.r4_nneg_5Fout = 0#1) (full : s.r1_nreq_5Fdw = 1) (high : s.r5_nisHi = 1)
    (reset : ∀ t, t < 64 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 64 → (inputs t).nio_5Fkill = 0) :
    (observe (run s inputs 64) (inputs 64)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s inputs 64) (inputs 64)).nio_5Fresp_5Fbits_5Ftag = s.r2_nreq_5Ftag ∧
    (observe (run s inputs 64) (inputs 64)).nio_5Fresp_5Fbits_5Fdata =
      BitVec.ofNat 64 (a.toNat * d.toNat / 2 ^ 64) := by
  have result := unsigned_product_state s inputs a d multiplying count divisor initial sign reset alive
  have before := multiplication_prefix s inputs multiplying 0 (by rw [count]; rfl) reset alive 63 (by omega)
  have counter : (run s inputs 63).r3_ncount = 63#7 := BitVec.eq_of_toNat_eq before.2.1
  have previousMetadata := metadata_run s inputs 63 (by
    intro t bound
    have traceFacts := multiplication_prefix s inputs multiplying 0 (by rw [count]; rfl) reset alive t (by omega)
    rw [traceFacts.1]
    decide)
  have mode : (run s inputs 64).r6_nresHi = 1 :=
    (select_multiply_response _ _ before.1 counter).trans
      ((congrArg (fun m => m.2.2) previousMetadata).trans high)
  have width : (run s inputs 64).r1_nreq_5Fdw = 1 :=
    (congrArg (fun m => m.1) result.2.2).trans full
  have output := observe_high_product (run s inputs 64) (inputs 64) result.1 width mode
  refine ⟨output.1, output.2.1.trans (congrArg (fun m => m.2.1) result.2.2), ?_⟩
  rw [output.2.2]
  apply BitVec.eq_of_toNat_eq
  rw [unpack_high, result.2.1]
  rfl

/-- An accepted MULHU request produces the upper half of the exact product
    after one acceptance edge and 64 computation edges. -/
theorem unsigned_high_accepted (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (full : (inputs 0).nio_5Freq_5Fbits_5Fdw = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 3#4)
    (reset : ∀ t, t < 65 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 65 → (inputs t).nio_5Fkill = 0) :
    (observe (run s inputs 65) (inputs 65)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s inputs 65) (inputs 65)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag ∧
    (observe (run s inputs 65) (inputs 65)).nio_5Fresp_5Fbits_5Fdata =
      BitVec.ofNat 64 ((inputs 0).nio_5Freq_5Fbits_5Fin1.toNat *
        (inputs 0).nio_5Freq_5Fbits_5Fin2.toNat / 2 ^ 64) := by
  have captured := capture_high_product s (inputs 0) idle valid (reset 0 (by omega)) full (Or.inr (Or.inr operation))
  simp only [operation, BitVec.reduceEq, if_false, if_true] at captured
  have output := unsigned_high_core_result (step s (inputs 0)) (fun t => inputs (1 + t)) _ _
    captured.1 captured.2.1 captured.2.2.1 captured.2.2.2.1 captured.2.2.2.2.1
    (congrArg (fun m => m.1) captured.2.2.2.2.2.2)
    (congrArg (fun m => m.2.2) captured.2.2.2.2.2.2)
    (by intro t h; exact reset (1 + t) (by omega))
    (by intro t h; exact alive (1 + t) (by omega))
  have trajectory := run_offset s inputs 1 64
  change run s inputs 65 = run (step s (inputs 0)) (fun t => inputs (1 + t)) 64 at trajectory
  rw [trajectory]
  exact ⟨output.1, output.2.1.trans (congrArg (fun m => m.2.1) captured.2.2.2.2.2.2), output.2.2⟩

theorem unsigned_high_after_reset (s : State) (resetInput : Inputs) (inputs : Nat → Inputs)
    (resetEdge : resetInput.nreset = 1) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (full : (inputs 0).nio_5Freq_5Fbits_5Fdw = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 3#4)
    (reset : ∀ t, t < 65 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 65 → (inputs t).nio_5Fkill = 0) :
    (observe (run (step s resetInput) inputs 65) (inputs 65)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run (step s resetInput) inputs 65) (inputs 65)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag ∧
    (observe (run (step s resetInput) inputs 65) (inputs 65)).nio_5Fresp_5Fbits_5Fdata =
      BitVec.ofNat 64 ((inputs 0).nio_5Freq_5Fbits_5Fin1.toNat *
        (inputs 0).nio_5Freq_5Fbits_5Fin2.toNat / 2 ^ 64) := by
  apply unsigned_high_accepted _ inputs _ valid full operation reset alive
  simp [step, eval_eq_spec, evalSpec, resetEdge]

#print axioms unsigned_high_after_reset
#print axioms unsigned_high_accepted
#print axioms unsigned_high_core_result
#print axioms observe_high_product
#print axioms unsigned_product_state
#print axioms unpack_high
end HierarchicalMulDiv
