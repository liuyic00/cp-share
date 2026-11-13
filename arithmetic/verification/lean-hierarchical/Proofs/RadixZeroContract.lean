import Proofs.RadixContract
import Proofs.RadixZeroArithmetic

namespace HierarchicalRadix
open DesignnRadix2Divider.nRadix2Divider

theorem capture_zero_flag (s : State) (i : Inputs)
    (idle : s.r0_nstate = 0) (valid : i.nio_5Fin_5Fvalid = 1)
    (zero : i.nio_5Fin_5Fbits_5Fsrc_5F1 = 0#64) :
    (step s i).r1_ndivBy0Reg = 1#1 := by
  simp [step, eval_eq_spec, evalSpec, v0, v1, v2, v20, v21, v22, v23, v24, idle, valid, zero]

theorem initialized_zero (s : State) (accept setup load : Inputs)
    (idle : s.r0_nstate = 0) (valid : accept.nio_5Fin_5Fvalid = 1)
    (r0 : accept.nreset = 0) (r1 : setup.nreset = 0) (r2 : load.nreset = 0)
    (zero : accept.nio_5Fin_5Fbits_5Fsrc_5F1 = 0#64) :
    let loaded := step (step (step s accept) setup) load
    loaded.r0_nstate = 3 ∧ loaded.r5_nbReg = 0#64 ∧ loaded.r9_ncnt_5Fvalue = 0#6 ∧
    loaded.r2_nshiftReg = (0#64 ++ magnitude accept.nio_5Fin_5Fbits_5Fsrc_5F0 accept.nctrl_5Fsign) ++ 0#1 := by
  have capture := capture_request s accept idle valid r0
  have fields := initialized_fields (step s accept) setup load capture.1 r1 r2
  have flag := capture_zero_flag s accept idle valid zero
  have count : v391 (step s accept) setup = 0#6 := by simp [v391, v62, flag]
  dsimp only
  refine ⟨fields.1, ?_, fields.2.2.2.1.trans count, ?_⟩
  · rw [fields.2.1, capture.2.1, zero]
    simp [magnitude, negativeFlag]
  · rw [fields.2.2.2.2, count, loadBits, capture.2.2.1]
    bv_decide

/-- The actual zero-divisor request reaches its specified magnitude result on
    edge 67, without constraining later data pins or downstream readiness. -/
theorem accepted_zero_magnitudes (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Fin_5Fvalid = 1)
    (reset : ∀ t, t < 67 → (inputs t).nreset = 0)
    (zero : (inputs 0).nio_5Fin_5Fbits_5Fsrc_5F1 = 0#64) :
    (observe (run s inputs 67) (inputs 67)).nio_5Fout_5Fvalid = 1 ∧
    BitVec.extractLsb' 0 64 (run s inputs 67).r2_nshiftReg = BitVec.allOnes 64 ∧
    BitVec.extractLsb' 65 64 (run s inputs 67).r2_nshiftReg =
      magnitude (inputs 0).nio_5Fin_5Fbits_5Fsrc_5F0 (inputs 0).nctrl_5Fsign := by
  have fields := initialized_zero s (inputs 0) (inputs 1) (inputs 2) idle valid
    (reset 0 (by omega)) (reset 1 (by omega)) (reset 2 (by omega)) zero
  let loaded := run s inputs 3
  have count : loaded.r9_ncnt_5Fvalue = 0#6 := fields.2.2.1
  have complete := computing_finishes loaded (fun t => inputs (3 + t)) fields.1
    (by intro t bound; apply reset; rw [count] at bound; change t < 64 at bound; omega)
  have cycles : 64 - loaded.r9_ncnt_5Fvalue.toNat = 64 := by rw [count]; rfl
  dsimp only at complete
  rw [cycles] at complete
  change (observe (run s inputs (3 + 64)) (inputs (3 + 64))).nio_5Fout_5Fvalid = 1 ∧ _
  rw [run_offset]
  refine ⟨complete.2.1, ?_⟩
  change BitVec.extractLsb' 0 64 (run s inputs (3 + 64)).r2_nshiftReg = _ ∧ _
  rw [run_offset, complete.2.2]
  change BitVec.extractLsb' 0 64 (advanceMany loaded.r5_nbReg 64 loaded.r2_nshiftReg) = _ ∧ _
  rw [show loaded.r5_nbReg = 0#64 from fields.2.1,
      show loaded.r2_nshiftReg = _ from fields.2.2.2]
  exact zero_result _

#print axioms accepted_zero_magnitudes
end HierarchicalRadix
