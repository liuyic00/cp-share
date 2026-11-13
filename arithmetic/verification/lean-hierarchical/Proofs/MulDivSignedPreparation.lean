import Proofs.MulDivUnsignedOutput

namespace HierarchicalMulDiv
open DesignnMulDiv.nMulDiv

attribute [local simp] v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v105 v106 v107 v108 v109 v110 v111 v112 v113 v114 v115 v116 v117 v118 v119 v120 v121 v122 v123 v124 v125 v126 v127 v128 v129 v130 v131 v132 v133 v134 v135 v136 v137 v138 v139 v140 v141 v142 v143 v144 v145 v146 v147 v148 v149 v150 v151

def signedOperand (x : BitVec 64) (dw : BitVec 1) : BitVec 64 :=
  if dw = 1 then x else (BitVec.extractLsb' 0 32 x).signExtend 64

def operandSign (x : BitVec 64) : BitVec 1 := BitVec.extractLsb' 63 1 x

def absoluteWord (x : BitVec 64) : BitVec 64 :=
  if operandSign x = 1 then -x else x

/-- Signed requests capture sign-extended word operands and the correction bit
    required for the requested quotient or remainder. -/
theorem capture_signed (s : State) (i : Inputs)
    (idle : s.r0_nstate = 0) (valid : i.nio_5Freq_5Fvalid = 1) (reset : i.nreset = 0)
    (operation : i.nio_5Freq_5Fbits_5Ffn = 4#4 ∨ i.nio_5Freq_5Fbits_5Ffn = 6#4) :
    let a := signedOperand i.nio_5Freq_5Fbits_5Fin1 i.nio_5Freq_5Fbits_5Fdw
    let b := signedOperand i.nio_5Freq_5Fbits_5Fin2 i.nio_5Freq_5Fbits_5Fdw
    (step s i).r0_nstate = (if (operandSign a ||| operandSign b) = 1 then 1 else 3) ∧
    (step s i).r6_nresHi = 0 ∧
    (step s i).r3_ncount = 0#7 ∧ (step s i).r7_ndivisor = operandSign b ++ b ∧
    (step s i).r8_nremainder = 0#66 ++ a ∧
    (step s i).r4_nneg_5Fout = (if i.nio_5Freq_5Fbits_5Ffn = 6#4 then operandSign a else operandSign a ^^^ operandSign b) ∧
    (step s i).r5_nisHi = (if i.nio_5Freq_5Fbits_5Ffn = 6#4 then 1#1 else 0#1) ∧
    (step s i).r1_nreq_5Fdw = i.nio_5Freq_5Fbits_5Fdw ∧
    (step s i).r2_nreq_5Ftag = i.nio_5Freq_5Fbits_5Ftag := by
  rcases operation with operation | operation
  all_goals simp [step, eval_eq_spec, evalSpec, idle, valid, reset, operation, signedOperand, operandSign]
  all_goals bv_decide

/-- The optional normalization edge handles both minimum signed operands and
    ordinary negative operands without an unbounded-integer overflow premise. -/
theorem normalize_edge (s : State) (i : Inputs) (a b : BitVec 64)
    (normalizing : s.r0_nstate = 1) (count : s.r3_ncount = 0#7)
    (selectLow : s.r6_nresHi = 0)
    (divisor : s.r7_ndivisor = operandSign b ++ b)
    (dividend : s.r8_nremainder = 0#66 ++ a)
    (reset : i.nreset = 0) (alive : i.nio_5Fkill = 0) :
    (step s i).r0_nstate = 3 ∧ (step s i).r3_ncount = 0#7 ∧
    (step s i).r7_ndivisor = 0#1 ++ absoluteWord b ∧
    (step s i).r8_nremainder = 0#66 ++ absoluteWord a ∧
    (step s i).r4_nneg_5Fout = s.r4_nneg_5Fout ∧ metadata (step s i) = metadata s := by
  simp only [operandSign] at divisor
  simp [step, eval_eq_spec, evalSpec, normalizing, count, selectLow, divisor, dividend,
    reset, alive, absoluteWord, operandSign, metadata]
  bv_decide

/-- A negative result is corrected only after the magnitude computation has
    finished. The selected quotient or remainder moves into the low word. -/
theorem correction_edge (s : State) (i : Inputs)
    (correcting : s.r0_nstate = 5) (reset : i.nreset = 0)
    (alive : i.nio_5Fkill = 0) :
    (step s i).r0_nstate = 7 ∧ (step s i).r6_nresHi = 0 ∧
    (step s i).r8_nremainder = 0#66 ++
      (-(if s.r6_nresHi = 1 then BitVec.extractLsb' 65 64 s.r8_nremainder
         else BitVec.extractLsb' 0 64 s.r8_nremainder)) ∧
    metadata (step s i) = metadata s := by
  simp [step, eval_eq_spec, evalSpec, correcting, reset, alive, metadata]

/-- With nonnegative operands, normalization is the identity. -/
theorem absolute_nonnegative (a b : BitVec 64)
    (signs : (operandSign a ||| operandSign b) ≠ 1#1) :
    absoluteWord a = a ∧ absoluteWord b = b := by
  simp only [absoluteWord, operandSign] at *
  bv_decide

/-- Both signed setup paths establish the same magnitude interface. The
    optional second edge is taken exactly when an operand has its sign bit set. -/
theorem prepare_signed (s : State) (accept next : Inputs)
    (idle : s.r0_nstate = 0) (valid : accept.nio_5Freq_5Fvalid = 1)
    (reset : accept.nreset = 0) (nextReset : next.nreset = 0)
    (alive : next.nio_5Fkill = 0)
    (operation : accept.nio_5Freq_5Fbits_5Ffn = 4#4 ∨ accept.nio_5Freq_5Fbits_5Ffn = 6#4) :
    let a := signedOperand accept.nio_5Freq_5Fbits_5Fin1 accept.nio_5Freq_5Fbits_5Fdw
    let b := signedOperand accept.nio_5Freq_5Fbits_5Fin2 accept.nio_5Freq_5Fbits_5Fdw
    let captured := step s accept
    let ready := if (operandSign a ||| operandSign b) = 1 then step captured next else captured
    ready.r0_nstate = 3 ∧ ready.r3_ncount = 0#7 ∧
    ready.r7_ndivisor = 0#1 ++ absoluteWord b ∧
    ready.r8_nremainder = 0#66 ++ absoluteWord a ∧
    ready.r4_nneg_5Fout = (if accept.nio_5Freq_5Fbits_5Ffn = 6#4 then operandSign a else operandSign a ^^^ operandSign b) ∧
    metadata ready = (accept.nio_5Freq_5Fbits_5Fdw, accept.nio_5Freq_5Fbits_5Ftag,
      if accept.nio_5Freq_5Fbits_5Ffn = 6#4 then 1#1 else 0#1) := by
  dsimp only
  rcases capture_signed s accept idle valid reset operation with
    ⟨state, low, count, divisor, dividend, sign, high, width, tag⟩
  have metadataFacts : metadata (step s accept) = (accept.nio_5Freq_5Fbits_5Fdw,
      accept.nio_5Freq_5Fbits_5Ftag, if accept.nio_5Freq_5Fbits_5Ffn = 6#4 then 1#1 else 0#1) := by
    simp only [metadata, width, tag, high]
  split
  · rename_i negative
    have norm := normalize_edge (step s accept) next _ _
      (by simpa only [negative, if_pos] using state) count low divisor dividend nextReset alive
    exact ⟨norm.1, norm.2.1, norm.2.2.1, norm.2.2.2.1,
      norm.2.2.2.2.1.trans sign, norm.2.2.2.2.2.trans metadataFacts⟩
  · rename_i positive
    have abs := absolute_nonnegative _ _ positive
    have signB : operandSign (signedOperand accept.nio_5Freq_5Fbits_5Fin2 accept.nio_5Freq_5Fbits_5Fdw) = 0#1 := by
      bv_decide
    refine ⟨?_, count, ?_, ?_, sign, metadataFacts⟩
    · simpa only [positive, if_neg] using state
    · simpa only [abs.2, signB] using divisor
    · simpa only [abs.1] using dividend

/-- Division by zero suppresses quotient sign correction so the all-ones
    magnitude remains all ones; remainder sign correction is retained. -/
theorem leading_sign (s : State) (i : Inputs) (a d : BitVec 64)
    (dividing : s.r0_nstate = 3) (count : s.r3_ncount = 0#7)
    (divisor : s.r7_ndivisor = 0#1 ++ d)
    (dividend : s.r8_nremainder = 0#66 ++ a) :
    (step s i).r4_nneg_5Fout =
      if d = 0#64 ∧ s.r5_nisHi = 0#1 then 0#1 else s.r4_nneg_5Fout := by
  simp [step, eval_eq_spec, evalSpec, dividing, count, divisor, dividend]
  bv_decide

/-- After the leading digit, the chosen correction bit remains unchanged. -/
theorem division_sign_stable (s : State) (i : Inputs)
    (dividing : s.r0_nstate = 3) (count : s.r3_ncount ≠ 0#7) :
    (step s i).r4_nneg_5Fout = s.r4_nneg_5Fout := by
  simp [step, eval_eq_spec, evalSpec, dividing, count]
  bv_decide

#print axioms leading_sign
#print axioms division_sign_stable
#print axioms prepare_signed
#print axioms correction_edge
#print axioms capture_signed
#print axioms normalize_edge
end HierarchicalMulDiv
