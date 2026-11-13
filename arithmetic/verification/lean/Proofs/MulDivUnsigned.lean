import Proofs.MulDivOutput

namespace MulDivUnsigned
open nMulDiv
open MulDivDivision (packed)
open MulDivOutput (metadata)

def operand (i : Inputs) (x : BitVec 64) : BitVec 64 :=
  if i.nio_5Freq_5Fbits_5Fdw = 1 then x else (x.extractLsb' 0 32).zeroExtend 64

def format (width : BitVec 1) (x : BitVec 64) : BitVec 64 :=
  if width = 1 then x else (x.extractLsb' 0 32).signExtend 64

def specification (i : Inputs) : BitVec 64 :=
  let a := operand i i.nio_5Freq_5Fbits_5Fin1
  let d := operand i i.nio_5Freq_5Fbits_5Fin2
  format i.nio_5Freq_5Fbits_5Fdw
    (if i.nio_5Freq_5Fbits_5Ffn = 7 then BitVec.ofNat 64 (a.toNat % d.toNat)
     else if d = 0 then BitVec.allOnes 64 else BitVec.ofNat 64 (a.toNat / d.toNat))

/-- Unsigned word operands are zero-extended before division; the response
word is sign-extended only after quotient/remainder selection. -/
theorem capture (s : State) (i : Inputs)
    (idle : s.r0_nstate = 0) (valid : i.nio_5Freq_5Fvalid = 1) (reset : i.nreset = 0)
    (operation : i.nio_5Freq_5Fbits_5Ffn = 5 ∨ i.nio_5Freq_5Fbits_5Ffn = 7) :
    (step s i).r0_nstate = 3 ∧ (step s i).r3_ncount = 0 ∧
    (step s i).r7_ndivisor = 0#1 ++ operand i i.nio_5Freq_5Fbits_5Fin2 ∧
    packed (step s i) = 0#65 ++ operand i i.nio_5Freq_5Fbits_5Fin1 ∧
    (step s i).r4_nneg_5Fout = 0 ∧
    metadata (step s i) = (i.nio_5Freq_5Fbits_5Fdw, i.nio_5Freq_5Fbits_5Ftag,
      if i.nio_5Freq_5Fbits_5Ffn = 7 then 1 else 0) := by
  rcases operation with operation | operation <;>
    simp only [step, eval, packed, operand, metadata, idle, valid, reset, operation, Prod.mk.injEq] <;> bv_decide

theorem observe_format (s : State) (i : Inputs) (state : s.r0_nstate = 7) :
    (observe s i).nio_5Fresp_5Fbits_5Fdata = format s.r1_nreq_5Fdw
      (if s.r6_nresHi = 1 then (packed s).extractLsb' 65 64 else (packed s).extractLsb' 0 64) ∧
    (observe s i).nio_5Fresp_5Fbits_5Ftag = s.r2_nreq_5Ftag := by
  simp only [observe, eval, state, format, packed]
  bv_decide

/-- All magnitude inputs, including zero, starting at the actual captured
unsigned division state. This is shared by both word and full-width modes. -/
theorem magnitudes (s : State) (inputs : Nat → Inputs) (a d : BitVec 64)
    (state : s.r0_nstate = 3) (count : s.r3_ncount = 0)
    (divisor : s.r7_ndivisor = 0#1 ++ d) (initial : packed s = 0#65 ++ a)
    (reset : ∀ t, t < 65 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 65 → (inputs t).nio_5Fkill = 0) :
    (packed (run s inputs 65)).extractLsb' 0 64 =
      (if d = 0 then BitVec.allOnes 64 else BitVec.ofNat 64 (a.toNat / d.toNat)) ∧
    (packed (run s inputs 65)).extractLsb' 65 64 = BitVec.ofNat 64 (a.toNat % d.toNat) := by
  by_cases zero : d = 0
  · have divisorZero : s.r7_ndivisor = 0 := by rw [divisor, zero]; rfl
    have initialNat : (packed s).toNat = a.toNat := by rw [initial, BitVec.toNat_append]; simp
    have result := MulDivZero.zero_magnitudes s inputs a state count divisorZero initialNat reset kill
    simpa [zero] using result
  · have positive : 0 < d.toNat := by
      have notZero : d.toNat ≠ 0 := by
        intro h
        apply zero
        exact BitVec.eq_of_toNat_eq h
      omega
    have result := MulDivDivision.full_magnitude_result s inputs a d state count divisor positive initial reset kill
    have q := congrArg (BitVec.ofNat 64) result.1
    have r := congrArg (BitVec.ofNat 64) result.2
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at q r
    simpa only [zero, if_false] using And.intro q r

/-- Every DIVU/REMU and DIVUW/REMUW request produces the specified valid
response and tag after 65 further rising edges. Live request pins and response
readiness may change freely; reset and kill must remain deasserted. -/
theorem accepted_result (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 5 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 7)
    (reset : ∀ t, t < 66 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 66 → (inputs t).nio_5Fkill = 0) :
    (observe (run s inputs 66) (inputs 66)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s inputs 66) (inputs 66)).nio_5Fresp_5Fbits_5Fdata = specification (inputs 0) ∧
    (observe (run s inputs 66) (inputs 66)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag := by
  have captured := capture s (inputs 0) idle valid (reset 0 (by decide)) operation
  have finish : (run s inputs 66).r0_nstate = 7 ∧
      (run s inputs 66).r6_nresHi = (step s (inputs 0)).r5_nisHi ∧
      metadata (run s inputs 66) = metadata (step s (inputs 0)) := by
    rw [show 66 = 65 + 1 from rfl, MulDivControl.run_from_next]
    exact MulDivOutput.unsigned_finish _ _ captured.1 captured.2.1 captured.2.2.2.2.1
      (fun t h => reset (t + 1) (by omega)) (fun t h => kill (t + 1) (by omega))
  have arithmetic := magnitudes (step s (inputs 0)) (fun t => inputs (t + 1))
    (operand (inputs 0) (inputs 0).nio_5Freq_5Fbits_5Fin1)
    (operand (inputs 0) (inputs 0).nio_5Freq_5Fbits_5Fin2)
    captured.1 captured.2.1 captured.2.2.1 captured.2.2.2.1
    (fun t h => reset (t + 1) (by omega)) (fun t h => kill (t + 1) (by omega))
  rw [← MulDivControl.run_from_next s inputs 65] at arithmetic
  have captureMeta := captured.2.2.2.2.2
  have finalMeta := finish.2.2.trans captureMeta
  have width := congrArg (fun m => m.1) finalMeta
  have tag := congrArg (fun m => m.2.1) finalMeta
  dsimp only [metadata] at width tag
  have selection := finish.2.1.trans (congrArg (fun m => m.2.2) captureMeta)
  have output := observe_format (run s inputs 66) (inputs 66) finish.1
  refine ⟨MulDivControl.done_valid _ _ (Or.inr finish.1), ?_, output.2.trans tag⟩
  rw [output.1, width, selection, arithmetic.1, arithmetic.2]
  by_cases choose : (inputs 0).nio_5Freq_5Fbits_5Ffn = 7 <;>
    simp only [specification, choose, if_true, if_false] <;> simp

theorem after_reset_result (initial : State) (resetInput : Inputs)
    (resetEdge : resetInput.nreset = 1) (inputs : Nat → Inputs)
    (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 5 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 7)
    (reset : ∀ t, t < 66 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 66 → (inputs t).nio_5Fkill = 0) :
    (observe (run (step initial resetInput) inputs 66) (inputs 66)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run (step initial resetInput) inputs 66) (inputs 66)).nio_5Fresp_5Fbits_5Fdata = specification (inputs 0) ∧
    (observe (run (step initial resetInput) inputs 66) (inputs 66)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag := by
  exact accepted_result _ inputs (MulDivControl.reset_ready initial resetInput resetEdge)
    valid operation reset kill

end MulDivUnsigned
