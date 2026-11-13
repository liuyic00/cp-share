import Proofs.MulDivMultiplySpecification

namespace HierarchicalMulDiv
open DesignnMulDiv.nMulDiv

def arithmeticSpecification (i : Inputs) : BitVec 64 :=
  if i.nio_5Freq_5Fbits_5Ffn = 4#4 ∨ i.nio_5Freq_5Fbits_5Ffn = 6#4 then signedSpecification i
  else if i.nio_5Freq_5Fbits_5Ffn = 5#4 ∨ i.nio_5Freq_5Fbits_5Ffn = 7#4 then unsignedSpecification i
  else multiplicationSpecification i

def legalArithmetic (i : Inputs) : Prop :=
  (i.nio_5Freq_5Fbits_5Ffn = 0#4 ∨
    (i.nio_5Freq_5Fbits_5Fdw = 1 ∧
      (i.nio_5Freq_5Fbits_5Ffn = 1#4 ∨ i.nio_5Freq_5Fbits_5Ffn = 2#4 ∨ i.nio_5Freq_5Fbits_5Ffn = 3#4))) ∨
  (i.nio_5Freq_5Fbits_5Ffn = 4#4 ∨ i.nio_5Freq_5Fbits_5Ffn = 6#4) ∨
  (i.nio_5Freq_5Fbits_5Ffn = 5#4 ∨ i.nio_5Freq_5Fbits_5Ffn = 7#4)

/-- Every supported arithmetic request returns its specified result and tag
    within 68 edges, provided reset and kill do not interrupt the operation. -/
theorem arithmetic_accepted (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (legal : legalArithmetic (inputs 0))
    (reset : ∀ t, t < 68 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 68 → (inputs t).nio_5Fkill = 0) :
    ∃ n, 33 ≤ n ∧ n ≤ 68 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fvalid = 1 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Fdata = arithmeticSpecification (inputs 0) := by
  rcases legal with mul | signed | unsigned
  · have notSigned : ¬((inputs 0).nio_5Freq_5Fbits_5Ffn = 4#4 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 6#4) := by bv_decide
    have notUnsigned : ¬((inputs 0).nio_5Freq_5Fbits_5Ffn = 5#4 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 7#4) := by bv_decide
    have result := multiplication_accepted s inputs idle valid mul
      (by intro t h; exact reset t (by omega)) (by intro t h; exact alive t (by omega))
    refine ⟨multiplicationLatency (inputs 0), ?_, ?_, result.1, result.2.1, ?_⟩
    · unfold multiplicationLatency; split <;> omega
    · unfold multiplicationLatency; split <;> omega
    · simpa only [arithmeticSpecification, notSigned, notUnsigned, if_false] using result.2.2
  · obtain ⟨n, lower, upper, result⟩ := signed_accepted_result s inputs idle valid signed reset alive
    refine ⟨n, by omega, upper, result.1, result.2.1, ?_⟩
    simpa only [arithmeticSpecification, signed, if_true] using result.2.2
  · have notSigned : ¬((inputs 0).nio_5Freq_5Fbits_5Ffn = 4#4 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 6#4) := by bv_decide
    have result := unsigned_accepted_result s inputs idle valid unsigned
      (by intro t h; exact reset t (by omega)) (by intro t h; exact alive t (by omega))
    refine ⟨66, by omega, by omega, result.1, result.2.1, ?_⟩
    simpa only [arithmeticSpecification, notSigned, unsigned, if_false, if_true] using result.2.2

/-- The arithmetic contract starts from arbitrary data-register contents;
    one reset edge establishes the required idle control state. -/
theorem arithmetic_after_reset (s : State) (resetInput : Inputs) (inputs : Nat → Inputs)
    (resetEdge : resetInput.nreset = 1) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (legal : legalArithmetic (inputs 0))
    (reset : ∀ t, t < 68 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 68 → (inputs t).nio_5Fkill = 0) :
    ∃ n, 33 ≤ n ∧ n ≤ 68 ∧
      (observe (run (step s resetInput) inputs n) (inputs n)).nio_5Fresp_5Fvalid = 1 ∧
      (observe (run (step s resetInput) inputs n) (inputs n)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag ∧
      (observe (run (step s resetInput) inputs n) (inputs n)).nio_5Fresp_5Fbits_5Fdata = arithmeticSpecification (inputs 0) := by
  apply arithmetic_accepted _ inputs _ valid legal reset alive
  simp [step, eval_eq_spec, evalSpec, v0, resetEdge]

#print axioms arithmetic_after_reset
#print axioms arithmetic_accepted
end HierarchicalMulDiv
