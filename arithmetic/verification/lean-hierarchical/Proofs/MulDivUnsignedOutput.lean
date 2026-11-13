import Proofs.MulDivZeroExecution

namespace HierarchicalMulDiv
open DesignnMulDiv.nMulDiv

def unsignedSpecification (i : Inputs) : BitVec 64 :=
  let a := unsignedOperand i.nio_5Freq_5Fbits_5Fin1 i.nio_5Freq_5Fbits_5Fdw
  let b := unsignedOperand i.nio_5Freq_5Fbits_5Fin2 i.nio_5Freq_5Fbits_5Fdw
  formatUnsigned (if b = 0#64 then BitVec.allOnes 64 else BitVec.ofNat 64 (a.toNat / b.toNat))
    (BitVec.ofNat 64 (a.toNat % b.toNat)) i.nio_5Freq_5Fbits_5Fdw
    (if i.nio_5Freq_5Fbits_5Ffn = 7#4 then 1#1 else 0#1)

/-- Full nonzero unsigned request contract: acceptance, both word widths,
    arithmetic, quotient/remainder selection, output formatting and response tag. -/
theorem unsigned_nonzero_result (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 5#4 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 7#4)
    (reset : ∀ t, t < 66 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 66 → (inputs t).nio_5Fkill = 0)
    (nonzero : unsignedOperand (inputs 0).nio_5Freq_5Fbits_5Fin2 (inputs 0).nio_5Freq_5Fbits_5Fdw ≠ 0#64) :
    (observe (run s inputs 66) (inputs 66)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s inputs 66) (inputs 66)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag ∧
    (observe (run s inputs 66) (inputs 66)).nio_5Fresp_5Fbits_5Fdata = unsignedSpecification (inputs 0) := by
  let a := unsignedOperand (inputs 0).nio_5Freq_5Fbits_5Fin1 (inputs 0).nio_5Freq_5Fbits_5Fdw
  let b := unsignedOperand (inputs 0).nio_5Freq_5Fbits_5Fin2 (inputs 0).nio_5Freq_5Fbits_5Fdw
  have captured := capture_unsigned s (inputs 0) idle valid (reset 0 (by omega)) operation
  have prepared := prepare_unsigned s (inputs 0) (inputs 1) idle valid
    (reset 0 (by omega)) (reset 1 (by omega)) (alive 1 (by omega)) operation nonzero
  have positive : 0 < b.toNat := by
    have notZero : b.toNat ≠ 0 := by
      intro h
      apply nonzero
      apply BitVec.eq_of_toNat_eq
      exact h
    omega
  have nonnegative : (run s inputs 2).r4_nneg_5Fout = 0#1 :=
    nonnegative_edge _ _ captured.1 captured.2.2.2.2.1
  have capturedMeta : metadata (step s (inputs 0)) =
      ((inputs 0).nio_5Freq_5Fbits_5Fdw, (inputs 0).nio_5Freq_5Fbits_5Ftag,
       if (inputs 0).nio_5Freq_5Fbits_5Ffn = 7#4 then 1#1 else 0#1) := by
    unfold metadata
    rw [captured.2.2.2.2.2.1, captured.2.2.2.2.2.2.1, captured.2.2.2.2.2.2.2]
  have kept : metadata (run s inputs 2) = metadata (step s (inputs 0)) :=
    metadata_stable _ _ (by change (step s (inputs 0)).r0_nstate ≠ 0#3; rw [captured.1]; decide)
  have flags := kept.trans capturedMeta
  have result := unsigned_core_result (run s inputs 2) (fun t => inputs (2 + t)) a b
    prepared.1 prepared.2.1 prepared.2.2.1 prepared.2.2.2 nonnegative positive
    (by intro t h; exact reset (2 + t) (by omega))
    (by intro t h; exact alive (2 + t) (by omega))
  simp only [run_offset s inputs 2 64]
  refine ⟨result.1, result.2.1.trans (congrArg (fun f => f.2.1) flags), ?_⟩
  rw [result.2.2,
    show (run s inputs 2).r1_nreq_5Fdw = _ from congrArg (fun f => f.1) flags,
    show (run s inputs 2).r5_nisHi = _ from congrArg (fun f => f.2.2) flags]
  simp only [unsignedSpecification, nonzero, if_false]
  rfl

theorem unsigned_zero_result (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 5#4 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 7#4)
    (reset : ∀ t, t < 66 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 66 → (inputs t).nio_5Fkill = 0)
    (zero : unsignedOperand (inputs 0).nio_5Freq_5Fbits_5Fin2 (inputs 0).nio_5Freq_5Fbits_5Fdw = 0#64) :
    (observe (run s inputs 66) (inputs 66)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s inputs 66) (inputs 66)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag ∧
    (observe (run s inputs 66) (inputs 66)).nio_5Fresp_5Fbits_5Fdata = unsignedSpecification (inputs 0) := by
  have captured := capture_unsigned s (inputs 0) idle valid (reset 0 (by omega)) operation
  have divisor : (step s (inputs 0)).r7_ndivisor = 0#65 := by
    rw [captured.2.2.1, zero]
    rfl
  have result := zero_core_result (step s (inputs 0)) (fun t => inputs (1 + t)) _
    captured.1 captured.2.1 divisor captured.2.2.2.1 captured.2.2.2.2.1
    (by intro t h; exact reset (1 + t) (by omega))
    (by intro t h; exact alive (1 + t) (by omega))
  simp only [run_offset s inputs 1 65]
  refine ⟨result.1, result.2.1.trans captured.2.2.2.2.2.2.2, ?_⟩
  change (observe (run (step s (inputs 0)) (fun t => inputs (1 + t)) 65) (inputs 66)).nio_5Fresp_5Fbits_5Fdata = _
  rw [result.2.2, captured.2.2.2.2.2.2.1, captured.2.2.2.2.2.1]
  simp [unsignedSpecification, zero]

theorem unsigned_accepted_result (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 5#4 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 7#4)
    (reset : ∀ t, t < 66 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 66 → (inputs t).nio_5Fkill = 0) :
    (observe (run s inputs 66) (inputs 66)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run s inputs 66) (inputs 66)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag ∧
    (observe (run s inputs 66) (inputs 66)).nio_5Fresp_5Fbits_5Fdata = unsignedSpecification (inputs 0) := by
  by_cases zero : unsignedOperand (inputs 0).nio_5Freq_5Fbits_5Fin2 (inputs 0).nio_5Freq_5Fbits_5Fdw = 0#64
  · exact unsigned_zero_result s inputs idle valid operation reset alive zero
  · exact unsigned_nonzero_result s inputs idle valid operation reset alive zero

theorem unsigned_after_reset_result (s : State) (resetInput : Inputs) (inputs : Nat → Inputs)
    (resetEdge : resetInput.nreset = 1) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 5#4 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 7#4)
    (reset : ∀ t, t < 66 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 66 → (inputs t).nio_5Fkill = 0) :
    (observe (run (step s resetInput) inputs 66) (inputs 66)).nio_5Fresp_5Fvalid = 1 ∧
    (observe (run (step s resetInput) inputs 66) (inputs 66)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag ∧
    (observe (run (step s resetInput) inputs 66) (inputs 66)).nio_5Fresp_5Fbits_5Fdata = unsignedSpecification (inputs 0) := by
  apply unsigned_accepted_result _ inputs _ valid operation reset alive
  simp [step, eval_eq_spec, evalSpec, v0, resetEdge]

#print axioms unsigned_after_reset_result
#print axioms unsigned_nonzero_result
end HierarchicalMulDiv
