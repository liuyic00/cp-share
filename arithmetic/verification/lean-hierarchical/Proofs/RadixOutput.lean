import Proofs.RadixZeroContract
import Proofs.RadixFlags

namespace HierarchicalRadix
open DesignnRadix2Divider.nRadix2Divider

def requestFlags (i : Inputs) : BitVec 1 × BitVec 1 × BitVec 1 × BitVec 1 :=
  let a := negativeFlag i.nio_5Fin_5Fbits_5Fsrc_5F0 i.nctrl_5Fsign
  let b := negativeFlag i.nio_5Fin_5Fbits_5Fsrc_5F1 i.nctrl_5Fsign
  (a, (a ^^^ b) &&& (if i.nio_5Fin_5Fbits_5Fsrc_5F1 ≠ 0#64 then 1#1 else 0#1),
    i.nctrl_5FisW, i.nctrl_5FisHi)

theorem capture_flags (s : State) (i : Inputs)
    (idle : s.r0_nstate = 0) (valid : i.nio_5Fin_5Fvalid = 1) (reset : i.nreset = 0) :
    flags (step s i) = requestFlags i := by
  have captured := (capture_request s i idle valid reset).2.2.2
  simp only [flags, requestFlags]
  rw [captured.1, captured.2.1, captured.2.2.1, captured.2.2.2]

def formatWords (q r : BitVec 64) (f : BitVec 1 × BitVec 1 × BitVec 1 × BitVec 1) : BitVec 64 :=
  let selected := if f.2.2.2 = 1 then (if f.1 = 1 then -r else r)
                  else (if f.2.1 = 1 then -q else q)
  if f.2.2.1 = 1 then (BitVec.extractLsb' 0 32 selected).signExtend 64 else selected

def specification (i : Inputs) : BitVec 64 :=
  let a := magnitude i.nio_5Fin_5Fbits_5Fsrc_5F0 i.nctrl_5Fsign
  let b := magnitude i.nio_5Fin_5Fbits_5Fsrc_5F1 i.nctrl_5Fsign
  formatWords (if i.nio_5Fin_5Fbits_5Fsrc_5F1 = 0#64 then BitVec.allOnes 64
    else BitVec.ofNat 64 (a.toNat / b.toNat))
    (BitVec.ofNat 64 (a.toNat % b.toNat)) (requestFlags i)

theorem observe_words (s : State) (i : Inputs) :
    (observe s i).nio_5Fout_5Fbits_5Fdata = formatWords
      (BitVec.extractLsb' 0 64 s.r2_nshiftReg) (BitVec.extractLsb' 65 64 s.r2_nshiftReg) (flags s) := by
  rw [output_format]
  rfl

/-- Complete request-to-response arithmetic contract, including signed
    overflow, division by zero, quotient/remainder selection and word mode. -/
theorem accepted_result (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Fin_5Fvalid = 1)
    (reset : ∀ t, t < 67 → (inputs t).nreset = 0) :
    ∃ n, 4 ≤ n ∧ n ≤ 67 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fout_5Fvalid = 1 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fout_5Fbits_5Fdata = specification (inputs 0) := by
  have metadata := (accepted_flags s inputs idle valid reset).trans
    (capture_flags s (inputs 0) idle valid (reset 0 (by omega)))
  by_cases zero : (inputs 0).nio_5Fin_5Fbits_5Fsrc_5F1 = 0#64
  · obtain ⟨done, quotient, remainder⟩ := accepted_zero_magnitudes s inputs idle valid reset zero
    have count : (run s inputs 3).r9_ncnt_5Fvalue = 0#6 :=
      (initialized_zero s (inputs 0) (inputs 1) (inputs 2) idle valid
        (reset 0 (by omega)) (reset 1 (by omega)) (reset 2 (by omega)) zero).2.2.1
    rw [count] at metadata
    change flags (run s inputs 67) = requestFlags (inputs 0) at metadata
    refine ⟨67, by omega, by omega, done, ?_⟩
    rw [observe_words, quotient, remainder, metadata]
    simp [specification, zero, magnitude, negativeFlag]
  · obtain ⟨n, timing, lower, upper, done, quotient, remainder⟩ :=
      accepted_magnitudes s inputs idle valid reset zero
    have q := congrArg (BitVec.ofNat 64) quotient
    have r := congrArg (BitVec.ofNat 64) remainder
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at q r
    have flagsAt : flags (run s inputs n) = requestFlags (inputs 0) := by rw [timing]; exact metadata
    refine ⟨n, lower, upper, done, ?_⟩
    rw [observe_words, q, r, flagsAt]
    simp only [specification, zero, if_false]

/-- Reset is sufficient; no initial data-register values are assumed. -/
theorem after_reset_result (s : State) (resetInput : Inputs) (inputs : Nat → Inputs)
    (resetEdge : resetInput.nreset = 1) (valid : (inputs 0).nio_5Fin_5Fvalid = 1)
    (reset : ∀ t, t < 67 → (inputs t).nreset = 0) :
    ∃ n, 4 ≤ n ∧ n ≤ 67 ∧
      (observe (run (step s resetInput) inputs n) (inputs n)).nio_5Fout_5Fvalid = 1 ∧
      (observe (run (step s resetInput) inputs n) (inputs n)).nio_5Fout_5Fbits_5Fdata = specification (inputs 0) :=
  accepted_result _ inputs (reset_control s resetInput resetEdge) valid reset

#print axioms after_reset_result
end HierarchicalRadix
