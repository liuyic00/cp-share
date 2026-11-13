import Proofs.RadixExecution

namespace HierarchicalRadix
open DesignnRadix2Divider.nRadix2Divider

attribute [local simp] v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 v15 v16 v17 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 v28 v29 v30 v31 v32 v33 v34 v35 v36 v37 v38 v39 v40 v41 v42 v43 v44 v45 v46 v47 v48 v49 v50 v51 v52 v53 v54 v55 v56 v57 v58 v59 v60 v61

def negativeFlag (value : BitVec 64) (signedMode : BitVec 1) : BitVec 1 :=
  BitVec.extractLsb' 63 1 value &&& signedMode

def magnitude (value : BitVec 64) (signedMode : BitVec 1) : BitVec 64 :=
  if negativeFlag value signedMode = 1 then -value else value

/-- All arithmetic operands and result-format controls are captured on the
    accepting edge; the initial contents of the data registers are irrelevant. -/
theorem capture_request (s : State) (i : Inputs)
    (idle : s.r0_nstate = 0) (valid : i.nio_5Fin_5Fvalid = 1)
    (reset : i.nreset = 0) :
    (step s i).r0_nstate = 1 ∧
    (step s i).r5_nbReg = magnitude i.nio_5Fin_5Fbits_5Fsrc_5F1 i.nctrl_5Fsign ∧
    (step s i).r6_naValx2Reg = magnitude i.nio_5Fin_5Fbits_5Fsrc_5F0 i.nctrl_5Fsign ++ 0#1 ∧
    (step s i).r3_naSignReg = negativeFlag i.nio_5Fin_5Fbits_5Fsrc_5F0 i.nctrl_5Fsign ∧
    (step s i).r4_nqSignReg =
      ((negativeFlag i.nio_5Fin_5Fbits_5Fsrc_5F0 i.nctrl_5Fsign ^^^
        negativeFlag i.nio_5Fin_5Fbits_5Fsrc_5F1 i.nctrl_5Fsign) &&&
       (if i.nio_5Fin_5Fbits_5Fsrc_5F1 ≠ 0#64 then 1#1 else 0#1)) ∧
    (step s i).r7_nctrlReg_5FisW = i.nctrl_5FisW ∧
    (step s i).r8_nctrlReg_5FisHi = i.nctrl_5FisHi := by
  simp [step, eval_eq_spec, evalSpec, idle, valid, reset, magnitude, negativeFlag]

theorem reset_control (s : State) (i : Inputs) (reset : i.nreset = 1) :
    (step s i).r0_nstate = 0 := by
  simp [step, eval_eq_spec, evalSpec, reset]

theorem setup_control (s : State) (i : Inputs) (setup : s.r0_nstate = 1)
    (reset : i.nreset = 0) : (step s i).r0_nstate = 2 := by
  simp [step, eval_eq_spec, evalSpec, setup, reset]

theorem load_control (s : State) (i : Inputs) (loading : s.r0_nstate = 2)
    (reset : i.nreset = 0) :
    (step s i).r0_nstate = 3 ∧
    (step s i).r2_nshiftReg =
      0#1 ++ ((0#63 ++ s.r6_naValx2Reg) <<< s.r9_ncnt_5Fvalue.toNat) := by
  have count : (0#122 ++ s.r9_ncnt_5Fvalue).toNat = s.r9_ncnt_5Fvalue.toNat := by
    rw [BitVec.toNat_append]
    simp
  simp [step, eval_eq_spec, evalSpec, loading, reset, count]

def formatAnswer (bits : BitVec 129) (aNegative qNegative word remainder : BitVec 1) : BitVec 64 :=
  let quotient := BitVec.extractLsb' 0 64 bits
  let residual := BitVec.extractLsb' 65 64 bits
  let selected := if remainder = 1 then (if aNegative = 1 then -residual else residual)
                  else (if qNegative = 1 then -quotient else quotient)
  if word = 1 then (BitVec.extractLsb' 0 32 selected).signExtend 64 else selected

/-- The output mux restores signs and applies the requested word extension. -/
theorem output_format (s : State) (i : Inputs) :
    (observe s i).nio_5Fout_5Fbits_5Fdata = formatAnswer s.r2_nshiftReg
      s.r3_naSignReg s.r4_nqSignReg s.r7_nctrlReg_5FisW s.r8_nctrlReg_5FisHi := by
  simp only [observe, eval_eq_spec, evalSpec, formatAnswer,
    v20, v40, v402, v403, v404, v405, v406, v407, v408, v409, v410, v411, v412]
  bv_decide

theorem run_offset (s : State) (inputs : Nat → Inputs) (start n : Nat) :
    run s inputs (start + n) =
      run (run s inputs start) (fun t => inputs (start + t)) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change step (run s inputs (start + n)) (inputs (start + n)) =
      step (run (run s inputs start) (fun t => inputs (start + t)) n) (inputs (start + n))
    rw [ih]

/-- Every accepted request reaches a valid response within the interface's
    advertised bound, even for zero divisors and arbitrary output readiness. -/
theorem accepted_completion (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Fin_5Fvalid = 1)
    (reset : ∀ t, t < 67 → (inputs t).nreset = 0) :
    ∃ n, 4 ≤ n ∧ n ≤ 67 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fout_5Fvalid = 1 := by
  have first : (run s inputs 1).r0_nstate = 1 :=
    (capture_request s (inputs 0) idle valid (reset 0 (by omega))).1
  have second : (run s inputs 2).r0_nstate = 2 :=
    setup_control _ (inputs 1) first (reset 1 (by omega))
  have third : (run s inputs 3).r0_nstate = 3 :=
    (load_control _ (inputs 2) second (reset 2 (by omega))).1
  let readyState := run s inputs 3
  let cycles := 64 - readyState.r9_ncnt_5Fvalue.toNat
  have width := readyState.r9_ncnt_5Fvalue.isLt
  have lower : 1 ≤ cycles := by dsimp [cycles]; omega
  have upper : cycles ≤ 64 := by dsimp [cycles]; omega
  have complete := computing_finishes readyState (fun t => inputs (3 + t)) third
    (by intro t bound; apply reset; dsimp [readyState] at bound; omega)
  refine ⟨3 + cycles, by omega, by omega, ?_⟩
  rw [run_offset]
  exact complete.2.1

#print axioms accepted_completion
#print axioms capture_request
#print axioms output_format
end HierarchicalRadix
