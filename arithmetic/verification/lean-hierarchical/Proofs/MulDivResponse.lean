import Proofs.MulDivRequest

namespace HierarchicalMulDiv
open DesignnMulDiv.nMulDiv

attribute [local simp] v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61 v62 v63 v64 v65 v66 v67 v68 v69 v70 v71 v72 v73 v74 v75 v76 v77 v78 v79 v80 v81 v82 v83 v84 v85 v86 v87 v88 v89 v90 v91 v92 v93 v94 v95 v96 v97 v98 v99 v100 v101 v102 v103 v104 v105 v106 v107 v108 v109 v110 v111 v112 v113 v114 v115 v116 v117 v118 v119 v120 v121 v122 v123 v124 v125 v126 v127 v128 v129 v130 v131 v132 v133 v134 v135 v136 v137 v138 v139 v140 v141 v142 v143 v144 v145 v146 v147 v148 v149 v150 v151 v152 v153 v154 v155 v156 v157 v158 v159 v160

def metadata (s : State) : BitVec 1 × BitVec 5 × BitVec 1 :=
  (s.r1_nreq_5Fdw, s.r2_nreq_5Ftag, s.r5_nisHi)

theorem metadata_stable (s : State) (i : Inputs) (active : s.r0_nstate ≠ 0#3) :
    metadata (step s i) = metadata s := by
  simp [metadata, step, eval_eq_spec, evalSpec, active]

theorem metadata_run (s : State) (inputs : Nat → Inputs) (n : Nat)
    (active : ∀ t, t < n → (run s inputs t).r0_nstate ≠ 0#3) :
    metadata (run s inputs n) = metadata s := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [run, metadata_stable _ _ (active n (by omega))]
    exact ih (by intro t h; exact active t (by omega))

theorem nonnegative_edge (s : State) (i : Inputs)
    (dividing : s.r0_nstate = 3) (nonnegative : s.r4_nneg_5Fout = 0#1) :
    (step s i).r4_nneg_5Fout = 0#1 := by
  simp [step, eval_eq_spec, evalSpec, dividing, nonnegative]

theorem nonnegative_run (s : State) (inputs : Nat → Inputs) (n : Nat)
    (nonnegative : s.r4_nneg_5Fout = 0#1)
    (active : ∀ t, t < n → (run s inputs t).r0_nstate = 3) :
    (run s inputs n).r4_nneg_5Fout = 0#1 := by
  induction n with
  | zero => exact nonnegative
  | succ n ih =>
    exact nonnegative_edge _ _ (active n (by omega))
      (ih (by intro t h; exact active t (by omega)))

def formatUnsigned (q r : BitVec 64) (dw hi : BitVec 1) : BitVec 64 :=
  let selected := if hi = 1 then r else q
  if dw = 1 then selected else (BitVec.extractLsb' 0 32 selected).signExtend 64

theorem observe_division (s : State) (i : Inputs) (responding : s.r0_nstate = 7) :
    (observe s i).nio_5Fresp_5Fvalid = 1 ∧
    (observe s i).nio_5Fresp_5Fbits_5Ftag = s.r2_nreq_5Ftag ∧
    (observe s i).nio_5Fresp_5Fbits_5Fdata = formatUnsigned
      (BitVec.extractLsb' 0 64 s.r8_nremainder)
      (BitVec.extractLsb' 65 64 s.r8_nremainder) s.r1_nreq_5Fdw s.r6_nresHi := by
  simp [observe, eval_eq_spec, evalSpec, responding, formatUnsigned]
  bv_decide

theorem select_response (s : State) (i : Inputs)
    (dividing : s.r0_nstate = 3) (last : s.r3_ncount = 64#7) :
    (step s i).r6_nresHi = s.r5_nisHi := by
  simp [step, eval_eq_spec, evalSpec, dividing, last]
  bv_decide

/-- The normalized unsigned computation produces a formatted, tagged response
    on its final edge, independently of downstream readiness. -/
theorem unsigned_core_result (s : State) (inputs : Nat → Inputs) (a d : BitVec 64)
    (dividing : s.r0_nstate = 3) (count : s.r3_ncount = 1#7)
    (divisor : s.r7_ndivisor = 0#1 ++ d)
    (initial : s.r8_nremainder = 0#1 ++ ((0#64 ++ a) ++ 0#1))
    (nonnegative : s.r4_nneg_5Fout = 0#1) (positive : 0 < d.toNat)
    (reset : ∀ t, t < 64 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 64 → (inputs t).nio_5Fkill = 0) :
    (observe (run s inputs 64) (inputs 64)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s inputs 64) (inputs 64)).nio_5Fresp_5Fbits_5Ftag = s.r2_nreq_5Ftag ∧
    (observe (run s inputs 64) (inputs 64)).nio_5Fresp_5Fbits_5Fdata =
      formatUnsigned (BitVec.ofNat 64 (a.toNat / d.toNat)) (BitVec.ofNat 64 (a.toNat % d.toNat))
        s.r1_nreq_5Fdw s.r5_nisHi := by
  let bits : BitVec 129 := (0#64 ++ a) ++ 0#1
  have bound : HierarchicalRadix.candidate bits < 2 * d.toNat := by
    rw [HierarchicalRadix.candidate_value]
    have value : bits.toNat = 2 * a.toNat := by
      dsimp [bits]
      rw [HierarchicalRadix.append_value, HierarchicalRadix.append_value]
      simp [Nat.mul_comm]
    rw [value]
    have width := a.isLt
    omega
  have active (t : Nat) (h : t < 64) : (run s inputs t).r0_nstate = 3 :=
    (division_prefix s inputs bits d dividing count divisor initial bound reset alive t h).1
  have finish := division_finish s inputs bits d dividing count divisor initial bound reset alive
  have sign := nonnegative_run s inputs 63 nonnegative (by intro t h; exact active t (by omega))
  have finished : (run s inputs 64).r0_nstate = 7 := by
    rw [finish.1, sign]
    rfl
  have lastCount : (run s inputs 63).r3_ncount = 64#7 := by
    apply BitVec.eq_of_toNat_eq
    exact (division_prefix s inputs bits d dividing count divisor initial bound reset alive 63 (by omega)).2.1
  have earlier := metadata_run s inputs 63 (by intro t h; rw [active t (by omega)]; decide)
  have later := metadata_run s inputs 64 (by intro t h; rw [active t h]; decide)
  have mode : (run s inputs 64).r6_nresHi = s.r5_nisHi :=
    (select_response _ _ (active 63 (by omega)) lastCount).trans (congrArg (fun f => f.2.2) earlier)
  have arithmetic := division_arithmetic s inputs a d dividing count divisor initial positive reset alive
  have q := congrArg (BitVec.ofNat 64) arithmetic.1
  have r := congrArg (BitVec.ofNat 64) arithmetic.2
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at q r
  have output := observe_division (run s inputs 64) (inputs 64) finished
  refine ⟨output.1, output.2.1.trans (congrArg (fun f => f.2.1) later), ?_⟩
  rw [output.2.2, q, r, mode, show (run s inputs 64).r1_nreq_5Fdw = s.r1_nreq_5Fdw from congrArg (fun f => f.1) later]

#print axioms unsigned_core_result
#print axioms observe_division
end HierarchicalMulDiv
