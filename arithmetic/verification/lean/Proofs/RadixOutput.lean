import Proofs.RadixZero

namespace nRadix2Divider
set_option maxRecDepth 4096

def requestMetadata (i : Inputs) : BitVec 1 × BitVec 1 × BitVec 1 × BitVec 1 :=
  let aNegative := (i.nctrl_5Fsign == 1) && i.nio_5Fin_5Fbits_5Fsrc_5F0.msb
  let bNegative := (i.nctrl_5Fsign == 1) && i.nio_5Fin_5Fbits_5Fsrc_5F1.msb
  (BitVec.ofBool aNegative,
   BitVec.ofBool (Bool.xor aNegative bNegative && (i.nio_5Fin_5Fbits_5Fsrc_5F1 != 0)),
   i.nctrl_5FisW, i.nctrl_5FisHi)

theorem capture_metadata (s : State) (i : Inputs)
    (idle : s.r0_nstate = 0) (valid : i.nio_5Fin_5Fvalid = 1) (reset : i.nreset = 0) :
    metadata (step s i) = requestMetadata i := by
  simp only [metadata, requestMetadata, step, eval, idle, valid, reset, Prod.mk.injEq]
  bv_decide

def formatResult (aNegative qNegative word remainder : BitVec 1) (q r : BitVec 64) : BitVec 64 :=
  let correctedQ := if qNegative = 1 then -q else q
  let correctedR := if aNegative = 1 then -r else r
  let selected := if remainder = 1 then correctedR else correctedQ
  if word = 1 then (BitVec.extractLsb' 0 32 selected).signExtend 64 else selected

theorem observe_format (s : State) (i : Inputs) :
    (observe s i).nio_5Fout_5Fbits_5Fdata =
      formatResult s.r3_naSignReg s.r4_nqSignReg s.r7_nctrlReg_5FisW s.r8_nctrlReg_5FisHi
        (BitVec.extractLsb' 0 64 s.r2_nshiftReg) (BitVec.extractLsb' 65 64 s.r2_nshiftReg) := by
  simp only [observe, eval, formatResult]
  bv_decide

/-- Signed/unsigned magnitude division, followed by sign restoration and the
    module's optional low-32-bit sign extension. Inputs are the accepted pins. -/
def specification (i : Inputs) : BitVec 64 :=
  let a := magnitude i.nio_5Fin_5Fbits_5Fsrc_5F0 i.nctrl_5Fsign
  let b := magnitude i.nio_5Fin_5Fbits_5Fsrc_5F1 i.nctrl_5Fsign
  let flags := requestMetadata i
  formatResult flags.1 flags.2.1 flags.2.2.1 flags.2.2.2
    (if i.nio_5Fin_5Fbits_5Fsrc_5F1 = 0 then BitVec.allOnes 64
     else BitVec.ofNat 64 (a.toNat / b.toNat))
    (BitVec.ofNat 64 (a.toNat % b.toNat))

/-- End-to-end correctness and bounded completion for every nonzero-divisor
    request, including signed overflow and the word-result formatting mode.
    Inputs and controls may change after acceptance; output ready is arbitrary. -/
theorem accepted_nonzero_result (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Fin_5Fvalid = 1)
    (reset : ∀ t, t < 67 → (inputs t).nreset = 0)
    (nonzero : (inputs 0).nio_5Fin_5Fbits_5Fsrc_5F1 ≠ 0) :
    ∃ n, 4 ≤ n ∧ n ≤ 67 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fout_5Fvalid = 1 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fout_5Fbits_5Fdata = specification (inputs 0) := by
  rcases accepted_magnitudes_correct s inputs idle valid reset nonzero with
    ⟨n, lower, upper, completed, quotient, remainder, flags⟩
  refine ⟨n, lower, upper, completed, ?_⟩
  have flags' := flags.trans (capture_metadata s (inputs 0) idle valid (reset 0 (by omega)))
  simp only [metadata, requestMetadata, Prod.mk.injEq] at flags'
  have q : BitVec.extractLsb' 0 64 (run s inputs n).r2_nshiftReg =
      BitVec.ofNat 64 ((magnitude (inputs 0).nio_5Fin_5Fbits_5Fsrc_5F0 (inputs 0).nctrl_5Fsign).toNat /
        (magnitude (inputs 0).nio_5Fin_5Fbits_5Fsrc_5F1 (inputs 0).nctrl_5Fsign).toNat) := by
    rw [← quotient, BitVec.ofNat_toNat]
    simp
  have r : BitVec.extractLsb' 65 64 (run s inputs n).r2_nshiftReg =
      BitVec.ofNat 64 ((magnitude (inputs 0).nio_5Fin_5Fbits_5Fsrc_5F0 (inputs 0).nctrl_5Fsign).toNat %
        (magnitude (inputs 0).nio_5Fin_5Fbits_5Fsrc_5F1 (inputs 0).nctrl_5Fsign).toNat) := by
    rw [← remainder, BitVec.ofNat_toNat]
    simp
  rw [observe_format, flags'.1, flags'.2.1, flags'.2.2.1, flags'.2.2.2, q, r]
  simp only [specification, nonzero, if_false]
  rfl

/-- Every divisor is covered, including zero. The output is the requested
    quotient/remainder, with sign and word formatting, within 66 further edges
    after the accepting edge. No downstream-readiness assumption is required. -/
theorem accepted_result (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Fin_5Fvalid = 1)
    (reset : ∀ t, t < 67 → (inputs t).nreset = 0) :
    ∃ n, 4 ≤ n ∧ n ≤ 67 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fout_5Fvalid = 1 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fout_5Fbits_5Fdata = specification (inputs 0) := by
  by_cases zero : (inputs 0).nio_5Fin_5Fbits_5Fsrc_5F1 = 0
  · rcases accepted_zero_magnitudes s inputs idle valid reset zero with
      ⟨completed, quotient, remainder, flags⟩
    refine ⟨67, by decide, by decide, completed, ?_⟩
    have flags' := flags.trans (capture_metadata s (inputs 0) idle valid (reset 0 (by omega)))
    simp only [metadata, requestMetadata, Prod.mk.injEq] at flags'
    rw [observe_format, flags'.1, flags'.2.1, flags'.2.2.1, flags'.2.2.2, quotient, remainder]
    simp [specification, requestMetadata, zero, magnitude]
  · exact accepted_nonzero_result s inputs idle valid reset zero
/-- Public reset-to-request contract: no initialization assumptions on any
    data register or assertion monitor are needed. -/
theorem after_reset_result (initial : State) (resetInput : Inputs) (inputs : Nat → Inputs)
    (resetEdge : resetInput.nreset = 1)
    (valid : (inputs 0).nio_5Fin_5Fvalid = 1)
    (reset : ∀ t, t < 67 → (inputs t).nreset = 0) :
    ∃ n, 4 ≤ n ∧ n ≤ 67 ∧
      (observe (run (step initial resetInput) inputs n) (inputs n)).nio_5Fout_5Fvalid = 1 ∧
      (observe (run (step initial resetInput) inputs n) (inputs n)).nio_5Fout_5Fbits_5Fdata =
        specification (inputs 0) :=
  accepted_result (step initial resetInput) inputs (reset_idle initial resetInput resetEdge) valid reset
end nRadix2Divider
