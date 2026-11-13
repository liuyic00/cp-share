import Proofs.MulDivCheckedDivisionMetadata

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

def UnsignedTimingInvariant (s : State) : Prop :=
  s.r9_ncontractPending = 1 → (s.r11_ncontractFn = 5#4 ∨ s.r11_ncontractFn = 7#4) →
    s.r4_nneg_5Fout = 0 ∧
    ((s.r0_nstate = 3 ∧ s.r3_ncount.ule 64 = true ∧ s.r10_ncontractAge = s.r3_ncount) ∨
      (s.r0_nstate = 7 ∧ s.r10_ncontractAge = 65))

theorem unsigned_timing_reset (s : State) (i : Inputs) (reset : i.nreset = 1) :
    UnsignedTimingInvariant (step s i) := by
  simp [UnsignedTimingInvariant, step, eval_eq_spec, evalSpec, reset, v8]

theorem unsigned_timing_preserved (s : State) (i : Inputs) (inv : UnsignedTimingInvariant s) :
    UnsignedTimingInvariant (step s i) := by
  unfold UnsignedTimingInvariant at inv ⊢
  simp only [step, eval_eq_spec, evalSpec, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61, v62, v63, v64, v65, v66, v67, v68, v69, v70, v71, v72, v73, v74, v75, v76, v77, v78, v79, v80, v81, v82, v83, v84, v85, v86, v87, v88, v89, v90, v91, v92, v152, v153, v154, v155, v156, v157, v158, v159, v160, v161, v162, v163, v164, v165, v166, v167, v168, v169, v170]
  bv_decide

theorem unsigned_timing_after_reset (s : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (inputs : Nat → Inputs) (n : Nat) :
    UnsignedTimingInvariant (run (step s resetInput) inputs n) := by
  induction n with
  | zero => exact unsigned_timing_reset s resetInput reset
  | succ n ih => exact unsigned_timing_preserved _ _ ih

theorem unsigned_timing_contract (s : State) (i : Inputs)
    (inv : UnsignedTimingInvariant s) (pending : s.r9_ncontractPending = 1)
    (operation : s.r11_ncontractFn = 5#4 ∨ s.r11_ncontractFn = 7#4) :
    s.r10_ncontractAge.ule (expectedAge s) = true ∧
      (v38 s i = 1 ↔ s.r10_ncontractAge = expectedAge s) := by
  have state := inv pending operation
  rw [unsigned_monitor_age s i operation]
  simp only [v38, v36, v37, v35, v4]
  bv_decide

end HierarchicalMulDivChecked
