import Proofs.MulDivCheckedDivisionMetadata

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

def SignedTimingInvariant (s : State) : Prop :=
  s.r9_ncontractPending = 1 → (s.r11_ncontractFn = 4#4 ∨ s.r11_ncontractFn = 6#4) →
    let i := recordedRequest s
    let pre := v226 s i
    let post := v225 s i
    let rawSign := if s.r11_ncontractFn = 6#4 then v214 s i else v214 s i ^^^ v216 s i
    s.r5_nisHi = v221 s i ∧
    ((s.r0_nstate = 1 ∧ pre = 1 ∧ s.r3_ncount = 0 ∧ s.r10_ncontractAge = 0 ∧
      s.r6_nresHi = 0 ∧ s.r4_nneg_5Fout = rawSign ∧
      s.r8_nremainder = 0#66 ++ v206 s i ∧ s.r7_ndivisor = v216 s i ++ v212 s i) ∨
    (s.r0_nstate = 3 ∧ s.r3_ncount.ule 64 = true ∧
      s.r10_ncontractAge = s.r3_ncount + (0#6 ++ pre) ∧
      ((s.r3_ncount = 0 → s.r4_nneg_5Fout = rawSign ∧
        s.r8_nremainder = 0#66 ++ v218 s i ∧ s.r7_ndivisor = 0#1 ++ v220 s i) ∧
       (s.r3_ncount ≠ 0 → s.r4_nneg_5Fout = post))) ∨
    (s.r0_nstate = 5 ∧ post = 1 ∧ s.r10_ncontractAge = 65 + (0#6 ++ pre)) ∨
    (s.r0_nstate = 7 ∧ s.r10_ncontractAge = 65 + (0#6 ++ pre) + (0#6 ++ post)))

theorem signed_timing_reset (s : State) (i : Inputs) (reset : i.nreset = 1) :
    SignedTimingInvariant (step s i) := by
  simp [SignedTimingInvariant, step, eval_eq_spec, evalSpec, reset, v8]

theorem signed_timing_preserved (s : State) (i : Inputs) (inv : SignedTimingInvariant s) :
    SignedTimingInvariant (step s i) := by
  unfold SignedTimingInvariant at inv ⊢
  dsimp only at inv ⊢
  simp only [recordedRequest, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114, v115, v116, v117, v118, v119, v120, v121, v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151, v152, v153, v154, v155, v156, v157, v158, v159, v160, v161, v162, v163, v164, v165, v166, v167, v168, v169, v170, v171, v172, v173, v174, v175, v176, v198, v199, v200, v201, v202, v203, v204, v205, v206, v207, v208, v209, v210, v211, v212, v213, v214, v215, v216, v217, v218, v219, v220, v221, v222, v223, v224, v225, v226, v227, v228, v229, v230, v231] at inv
  simp only [step, eval_eq_spec, evalSpec, recordedRequest, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v93, v94, v95, v96, v97, v98, v99, v100, v101, v102, v103, v104, v105, v106, v107, v108, v109, v110, v111, v112, v113, v114, v115, v116, v117, v118, v119, v120, v121, v140, v141, v142, v143, v144, v145, v146, v147, v148, v149, v150, v151, v152, v153, v154, v155, v156, v157, v158, v159, v160, v161, v162, v163, v164, v165, v166, v167, v168, v169, v170, v171, v172, v173, v174, v175, v176, v198, v199, v200, v201, v202, v203, v204, v205, v206, v207, v208, v209, v210, v211, v212, v213, v214, v215, v216, v217, v218, v219, v220, v221, v222, v223, v224, v225, v226, v227, v228, v229, v230, v231]
  bv_decide

theorem signed_timing_after_reset (s : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (inputs : Nat → Inputs) (n : Nat) :
    SignedTimingInvariant (run (step s resetInput) inputs n) := by
  induction n with
  | zero => exact signed_timing_reset s resetInput reset
  | succ n ih => exact signed_timing_preserved _ _ ih

theorem signed_timing_contract (s : State) (i : Inputs)
    (inv : SignedTimingInvariant s) (pending : s.r9_ncontractPending = 1)
    (operation : s.r11_ncontractFn = 4#4 ∨ s.r11_ncontractFn = 6#4) :
    s.r10_ncontractAge.ule (expectedAge s) = true ∧
      (v38 s i = 1 ↔ s.r10_ncontractAge = expectedAge s) := by
  have state := inv pending operation
  dsimp only at state
  have pre : v226 s (recordedRequest s) = v226 s i := by rfl
  have post : v225 s (recordedRequest s) = v225 s i := by rfl
  rw [pre, post] at state
  have division : v198 s i = 1 := by simp only [v198]; bv_decide
  rw [division_expected_age s i division]
  simp only [v38, v36, v37, v35, v4]
  bv_decide

end HierarchicalMulDivChecked
