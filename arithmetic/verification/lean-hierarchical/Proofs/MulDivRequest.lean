import Proofs.MulDivExecution

namespace HierarchicalMulDiv
open DesignnMulDiv.nMulDiv

attribute [local simp] v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v105 v106 v107 v108 v109 v110 v111 v112 v113 v114 v115 v116 v117 v118 v119 v120 v121 v122 v123 v124 v125 v126 v127 v128 v129 v130 v131 v132 v133 v134 v135 v136 v137 v138 v139 v140 v141 v142 v143 v144 v145 v146 v147 v148 v149 v150 v151

def unsignedOperand (x : BitVec 64) (dw : BitVec 1) : BitVec 64 :=
  if dw = 1 then x else 0#32 ++ BitVec.extractLsb' 0 32 x

/-- Unsigned division and remainder capture normalized operands in both full
    width and word modes, together with the response metadata. -/
theorem capture_unsigned (s : State) (i : Inputs)
    (idle : s.r0_nstate = 0) (valid : i.nio_5Freq_5Fvalid = 1)
    (reset : i.nreset = 0)
    (operation : i.nio_5Freq_5Fbits_5Ffn = 5#4 ∨ i.nio_5Freq_5Fbits_5Ffn = 7#4) :
    (step s i).r0_nstate = 3 ∧ (step s i).r3_ncount = 0#7 ∧
    (step s i).r7_ndivisor = 0#1 ++ unsignedOperand i.nio_5Freq_5Fbits_5Fin2 i.nio_5Freq_5Fbits_5Fdw ∧
    (step s i).r8_nremainder = 0#66 ++ unsignedOperand i.nio_5Freq_5Fbits_5Fin1 i.nio_5Freq_5Fbits_5Fdw ∧
    (step s i).r4_nneg_5Fout = 0#1 ∧
    (step s i).r5_nisHi = (if i.nio_5Freq_5Fbits_5Ffn = 7#4 then 1#1 else 0#1) ∧
    (step s i).r1_nreq_5Fdw = i.nio_5Freq_5Fbits_5Fdw ∧
    (step s i).r2_nreq_5Ftag = i.nio_5Freq_5Fbits_5Ftag := by
  rcases operation with operation | operation
  all_goals simp [step, eval_eq_spec, evalSpec, idle, valid, reset, operation, unsignedOperand]
  all_goals bv_decide

/-- The leading zero digit advances the packed dividend without subtraction. -/
theorem leading_digit (a d : BitVec 64) (nonzero : d ≠ 0#64) :
    divisionAdvance (0#66 ++ a) (0#1 ++ d) = 0#1 ++ ((0#64 ++ a) ++ 0#1) := by
  unfold divisionAdvance
  bv_decide

/-- Acceptance followed by the leading-digit edge establishes the exact
    preconditions of the 64-edge arithmetic proof. -/
theorem prepare_unsigned (s : State) (accept next : Inputs)
    (idle : s.r0_nstate = 0) (valid : accept.nio_5Freq_5Fvalid = 1)
    (reset : accept.nreset = 0) (nextReset : next.nreset = 0) (alive : next.nio_5Fkill = 0)
    (operation : accept.nio_5Freq_5Fbits_5Ffn = 5#4 ∨ accept.nio_5Freq_5Fbits_5Ffn = 7#4)
    (nonzero : unsignedOperand accept.nio_5Freq_5Fbits_5Fin2 accept.nio_5Freq_5Fbits_5Fdw ≠ 0#64) :
    let ready := step (step s accept) next
    ready.r0_nstate = 3 ∧ ready.r3_ncount = 1#7 ∧
    ready.r7_ndivisor = 0#1 ++ unsignedOperand accept.nio_5Freq_5Fbits_5Fin2 accept.nio_5Freq_5Fbits_5Fdw ∧
    ready.r8_nremainder = 0#1 ++ ((0#64 ++ unsignedOperand accept.nio_5Freq_5Fbits_5Fin1 accept.nio_5Freq_5Fbits_5Fdw) ++ 0#1) := by
  have captured := capture_unsigned s accept idle valid reset operation
  have control := division_control (step s accept) next captured.1 nextReset alive
  dsimp only
  refine ⟨?_, ?_, control.2.2.trans captured.2.2.1, ?_⟩
  · simpa [captured.2.1] using control.1
  · rw [control.2.1, captured.2.1]
    rfl
  · rw [division_edge _ _ captured.1, captured.2.2.1, captured.2.2.2.1]
    exact leading_digit _ _ nonzero

theorem run_offset (s : State) (inputs : Nat → Inputs) (start n : Nat) :
    run s inputs (start + n) = run (run s inputs start) (fun t => inputs (start + t)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step (run s inputs (start + n)) (inputs (start + n)) =
      step (run (run s inputs start) (fun t => inputs (start + t)) n) (inputs (start + n))
    rw [ih]

/-- Actual unsigned requests reach the exact quotient and remainder, including
    zero-extension of word operands; the divisor here is required nonzero. -/
theorem accepted_unsigned_magnitudes (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 5#4 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 7#4)
    (reset : ∀ t, t < 66 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 66 → (inputs t).nio_5Fkill = 0)
    (nonzero : unsignedOperand (inputs 0).nio_5Freq_5Fbits_5Fin2 (inputs 0).nio_5Freq_5Fbits_5Fdw ≠ 0#64) :
    let a := unsignedOperand (inputs 0).nio_5Freq_5Fbits_5Fin1 (inputs 0).nio_5Freq_5Fbits_5Fdw
    let b := unsignedOperand (inputs 0).nio_5Freq_5Fbits_5Fin2 (inputs 0).nio_5Freq_5Fbits_5Fdw
    (BitVec.extractLsb' 0 64 (run s inputs 66).r8_nremainder).toNat = a.toNat / b.toNat ∧
    (BitVec.extractLsb' 65 64 (run s inputs 66).r8_nremainder).toNat = a.toNat % b.toNat := by
  have prepared := prepare_unsigned s (inputs 0) (inputs 1) idle valid
    (reset 0 (by omega)) (reset 1 (by omega)) (alive 1 (by omega)) operation nonzero
  have positive : 0 < (unsignedOperand (inputs 0).nio_5Freq_5Fbits_5Fin2 (inputs 0).nio_5Freq_5Fbits_5Fdw).toNat := by
    have notZero : (unsignedOperand (inputs 0).nio_5Freq_5Fbits_5Fin2 (inputs 0).nio_5Freq_5Fbits_5Fdw).toNat ≠ 0 := by
      intro h
      apply nonzero
      apply BitVec.eq_of_toNat_eq
      exact h
    omega
  have arithmetic := division_arithmetic (run s inputs 2) (fun t => inputs (2 + t)) _ _
    prepared.1 prepared.2.1 prepared.2.2.1 prepared.2.2.2 positive
    (by intro t bound; exact reset (2 + t) (by omega))
    (by intro t bound; exact alive (2 + t) (by omega))
  dsimp only
  change (BitVec.extractLsb' 0 64 (run s inputs (2 + 64)).r8_nremainder).toNat = _ ∧ _
  rw [run_offset]
  exact arithmetic

#print axioms accepted_unsigned_magnitudes
#print axioms capture_unsigned
#print axioms leading_digit
end HierarchicalMulDiv
