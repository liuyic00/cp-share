import Proofs.RadixInitialization

namespace HierarchicalRadix
open DesignnRadix2Divider.nRadix2Divider

theorem magnitude_nonzero (value : BitVec 64) (mode : BitVec 1)
    (nonzero : value ≠ 0#64) : magnitude value mode ≠ 0#64 := by
  unfold magnitude
  split
  · intro zero
    exact nonzero (BitVec.neg_eq_zero_iff.mp zero)
  · exact nonzero

theorem capture_nonzero (s : State) (i : Inputs)
    (idle : s.r0_nstate = 0) (valid : i.nio_5Fin_5Fvalid = 1)
    (nonzero : i.nio_5Fin_5Fbits_5Fsrc_5F1 ≠ 0#64) :
    (step s i).r1_ndivBy0Reg = 0#1 := by
  simp [step, eval_eq_spec, evalSpec, idle, valid, nonzero, v0, v1, v2, v3, v4, v5, v6, v7, v8, v9, v10, v11, v12, v13, v14, v15, v16, v17, v18, v19, v20, v21, v22, v23, v24, v25, v26, v27, v28, v29, v30, v31, v32, v33, v34, v35, v36, v37, v38, v39, v40, v41, v42, v43, v44, v45, v46, v47, v48, v49, v50, v51, v52, v53, v54, v55, v56, v57, v58, v59, v60, v61]

/-- The real acceptance and setup edges establish every precondition of the
    generic restoring-division theorem. -/
theorem initialized_arithmetic (s : State) (accept setup load : Inputs)
    (idle : s.r0_nstate = 0) (valid : accept.nio_5Fin_5Fvalid = 1)
    (r0 : accept.nreset = 0) (r1 : setup.nreset = 0) (r2 : load.nreset = 0)
    (nonzero : accept.nio_5Fin_5Fbits_5Fsrc_5F1 ≠ 0#64) :
    let loaded := step (step (step s accept) setup) load
    let result := advanceMany loaded.r5_nbReg (64 - loaded.r9_ncnt_5Fvalue.toNat) loaded.r2_nshiftReg
    let a := magnitude accept.nio_5Fin_5Fbits_5Fsrc_5F0 accept.nctrl_5Fsign
    let b := magnitude accept.nio_5Fin_5Fbits_5Fsrc_5F1 accept.nctrl_5Fsign
    (BitVec.extractLsb' 0 64 result).toNat = a.toNat / b.toNat ∧
    (BitVec.extractLsb' 65 64 result).toNat = a.toNat % b.toNat := by
  let captured := step s accept
  let loaded := step (step captured setup) load
  have capture := capture_request s accept idle valid r0
  have state : captured.r0_nstate = 1 := capture.1
  have bNonzero : captured.r5_nbReg ≠ 0#64 := by
    rw [show captured.r5_nbReg = magnitude accept.nio_5Fin_5Fbits_5Fsrc_5F1 accept.nctrl_5Fsign from capture.2.1]
    exact magnitude_nonzero _ _ nonzero
  have fields := initialized_fields captured setup load state r1 r2
  have bound := initialized_bound captured setup load state r1 r2 bNonzero
    (capture_nonzero s accept idle valid nonzero)
  have scale : 2 ^ (64 - loaded.r9_ncnt_5Fvalue.toNat) * loaded.r2_nshiftReg.toNat =
      (magnitude accept.nio_5Fin_5Fbits_5Fsrc_5F0 accept.nctrl_5Fsign).toNat * 36893488147419103232 := by
    change 2 ^ (64 - (step (step captured setup) load).r9_ncnt_5Fvalue.toNat) *
      (step (step captured setup) load).r2_nshiftReg.toNat = _
    rw [fields.2.2.2.1, fields.2.2.2.2]
    change 2 ^ (64 - (v391 captured setup).toNat) *
      (0#1 ++ ((0#63 ++ captured.r6_naValx2Reg) <<< (v391 captured setup).toNat)).toNat = _
    rw [scaled_load]
    have aCapture : captured.r6_naValx2Reg =
        magnitude accept.nio_5Fin_5Fbits_5Fsrc_5F0 accept.nctrl_5Fsign ++ 0#1 := capture.2.2.1
    rw [aCapture, append_value]
    simp [Nat.mul_assoc]
  have arithmetic := completed_arithmetic loaded.r2_nshiftReg loaded.r5_nbReg
    (magnitude accept.nio_5Fin_5Fbits_5Fsrc_5F0 accept.nctrl_5Fsign).toNat
    (64 - loaded.r9_ncnt_5Fvalue.toNat) bound (by omega) scale
  have bCapture : loaded.r5_nbReg = magnitude accept.nio_5Fin_5Fbits_5Fsrc_5F1 accept.nctrl_5Fsign :=
    fields.2.1.trans capture.2.1
  dsimp only
  rw [← bCapture]
  exact arithmetic

/-- For every nonzero accepted divisor, the hardware produces the exact
    magnitude quotient and remainder within 67 edges. Later request pins and
    output readiness remain unconstrained. -/
theorem accepted_magnitudes (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Fin_5Fvalid = 1)
    (reset : ∀ t, t < 67 → (inputs t).nreset = 0)
    (nonzero : (inputs 0).nio_5Fin_5Fbits_5Fsrc_5F1 ≠ 0#64) :
    let a := magnitude (inputs 0).nio_5Fin_5Fbits_5Fsrc_5F0 (inputs 0).nctrl_5Fsign
    let b := magnitude (inputs 0).nio_5Fin_5Fbits_5Fsrc_5F1 (inputs 0).nctrl_5Fsign
    ∃ n, n = 3 + (64 - (run s inputs 3).r9_ncnt_5Fvalue.toNat) ∧ 4 ≤ n ∧ n ≤ 67 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fout_5Fvalid = 1 ∧
      (BitVec.extractLsb' 0 64 (run s inputs n).r2_nshiftReg).toNat = a.toNat / b.toNat ∧
      (BitVec.extractLsb' 65 64 (run s inputs n).r2_nshiftReg).toNat = a.toNat % b.toNat := by
  have first : (run s inputs 1).r0_nstate = 1 :=
    (capture_request s (inputs 0) idle valid (reset 0 (by omega))).1
  have fields := initialized_fields (run s inputs 1) (inputs 1) (inputs 2)
    first (reset 1 (by omega)) (reset 2 (by omega))
  let loaded := run s inputs 3
  have computing : loaded.r0_nstate = 3 := fields.1
  let cycles := 64 - loaded.r9_ncnt_5Fvalue.toNat
  have width := loaded.r9_ncnt_5Fvalue.isLt
  have lower : 1 ≤ cycles := by dsimp [cycles]; omega
  have upper : cycles ≤ 64 := by dsimp [cycles]; omega
  have complete := computing_finishes loaded (fun t => inputs (3 + t)) computing
    (by intro t bound; apply reset; omega)
  have arithmetic := initialized_arithmetic s (inputs 0) (inputs 1) (inputs 2)
    idle valid (reset 0 (by omega)) (reset 1 (by omega)) (reset 2 (by omega)) nonzero
  dsimp only
  refine ⟨3 + cycles, rfl, by omega, by omega, ?_, ?_⟩
  · rw [run_offset]
    exact complete.2.1
  · rw [run_offset, complete.2.2]
    exact arithmetic

#print axioms accepted_magnitudes
#print axioms initialized_arithmetic
end HierarchicalRadix
