import Proofs.RadixDatapath

namespace nRadix2Divider
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The actual leading-zero skip circuit establishes the restoring candidate
    bound, including a zero dividend and the highest-set-bit boundary. -/
theorem skip_initializes_bound (s : State) (i j : Inputs)
    (state : s.r0_nstate = 1) (reset : i.nreset = 0)
    (nextReset : j.nreset = 0) (nonzero : s.r5_nbReg ≠ 0)
    (flag : s.r1_ndivBy0Reg = 0) :
    candidate (step (step s i) j).r2_nshiftReg < 2 * s.r5_nbReg.toNat := by
  have bound : BitVec.extractLsb' 64 65 (step (step s i) j).r2_nshiftReg <
      (s.r5_nbReg ++ 0#1) := by
    simp only [step, eval, state, reset, nextReset, flag, ← BitVec.lt_def, ← BitVec.le_def]
    bv_decide (config := { timeout := 60 })
  change candidate (step (step s i) j).r2_nshiftReg < (s.r5_nbReg ++ 0#1).toNat at bound
  rw [BitVec.toNat_append] at bound
  simpa [Nat.shiftLeft_eq, Nat.mul_comm] using bound
/-- Acceptance captures a nonzero magnitude even for the most negative signed
    operand; no restriction on signed/unsigned control is needed. -/
theorem accept_nonzero (s : State) (i : Inputs)
    (idle : s.r0_nstate = 0) (valid : i.nio_5Fin_5Fvalid = 1)
    (reset : i.nreset = 0) (nonzero : i.nio_5Fin_5Fbits_5Fsrc_5F1 ≠ 0) :
    (step s i).r5_nbReg ≠ 0 ∧ (step s i).r1_ndivBy0Reg = 0 := by
  simp only [step, eval, idle, valid, reset]
  bv_decide

/-- The candidate bound is established from an actual accepted nonzero-divisor
    request, with arbitrary live pins on the subsequent setup cycles. -/
theorem accepted_initializes_bound (s : State) (accept log shift : Inputs)
    (idle : s.r0_nstate = 0) (valid : accept.nio_5Fin_5Fvalid = 1)
    (r0 : accept.nreset = 0) (r1 : log.nreset = 0) (r2 : shift.nreset = 0)
    (nonzero : accept.nio_5Fin_5Fbits_5Fsrc_5F1 ≠ 0) :
    let initialized := step (step (step s accept) log) shift
    candidate initialized.r2_nshiftReg < 2 * initialized.r5_nbReg.toNat := by
  let captured := step s accept
  have state : captured.r0_nstate = 1 := accept_state s accept idle r0 valid
  have inputs := accept_nonzero s accept idle valid r0 nonzero
  have preserved : (step (step captured log) shift).r5_nbReg = captured.r5_nbReg := by
    simp [step, eval, state, r1, r2]
  change candidate (step (step captured log) shift).r2_nshiftReg <
    2 * (step (step captured log) shift).r5_nbReg.toNat
  rw [preserved]
  exact skip_initializes_bound captured log shift state r1 r2 inputs.1 inputs.2
end nRadix2Divider
