import Proofs.MulDivNormalized

namespace HierarchicalMulDiv
open DesignnMulDiv.nMulDiv

def signedA (i : Inputs) := signedOperand i.nio_5Freq_5Fbits_5Fin1 i.nio_5Freq_5Fbits_5Fdw
def signedB (i : Inputs) := signedOperand i.nio_5Freq_5Fbits_5Fin2 i.nio_5Freq_5Fbits_5Fdw
def signedNegative (i : Inputs) : BitVec 1 :=
  if i.nio_5Freq_5Fbits_5Ffn = 6#4 then operandSign (signedA i)
  else operandSign (signedA i) ^^^ operandSign (signedB i)
def signedHigh (i : Inputs) : BitVec 1 := if i.nio_5Freq_5Fbits_5Ffn = 6#4 then 1 else 0

def signedSetupTime (i : Inputs) : Nat :=
  if (operandSign (signedA i) ||| operandSign (signedB i)) = 1 then 2 else 1

theorem signed_setup_time (i : Inputs) : signedSetupTime i = 1 ∨ signedSetupTime i = 2 := by
  unfold signedSetupTime
  split <;> simp

/-- Actual request traces reach the common magnitude interface after the
    acceptance edge and, exactly when needed, a normalization edge. -/
theorem signed_setup_run (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 4#4 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 6#4)
    (reset : ∀ t, t < 2 → (inputs t).nreset = 0)
    (alive : (inputs 1).nio_5Fkill = 0) :
    let ready := run s inputs (signedSetupTime (inputs 0))
    ready.r0_nstate = 3 ∧ ready.r3_ncount = 0#7 ∧
    ready.r7_ndivisor = 0#1 ++ absoluteWord (signedB (inputs 0)) ∧
    ready.r8_nremainder = 0#66 ++ absoluteWord (signedA (inputs 0)) ∧
    ready.r4_nneg_5Fout = signedNegative (inputs 0) ∧
    metadata ready = ((inputs 0).nio_5Freq_5Fbits_5Fdw, (inputs 0).nio_5Freq_5Fbits_5Ftag,
      signedHigh (inputs 0)) := by
  have prepared := prepare_signed s (inputs 0) (inputs 1) idle valid
    (reset 0 (by omega)) (reset 1 (by omega)) alive operation
  dsimp only [signedSetupTime, signedA, signedB, signedNegative, signedHigh]
  dsimp only at prepared
  split <;> rename_i path
  · simpa only [path, if_pos, run] using prepared
  · simpa only [path, if_neg, run] using prepared

def signedSpecification (i : Inputs) : BitVec 64 :=
  normalizedSpecification (absoluteWord (signedA i)) (absoluteWord (signedB i))
    i.nio_5Freq_5Fbits_5Fdw (signedHigh i) (signedNegative i)

/-- Every accepted signed division or remainder request reaches its complete
    formatted response, including zero divisors and minimum signed operands. -/
theorem signed_accepted_result (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 4#4 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 6#4)
    (reset : ∀ t, t < 68 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 68 → (inputs t).nio_5Fkill = 0) :
    ∃ n, 66 ≤ n ∧ n ≤ 68 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fvalid = 1 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Fdata = signedSpecification (inputs 0) := by
  let start := signedSetupTime (inputs 0)
  have setupTime := signed_setup_time (inputs 0)
  have prepared := signed_setup_run s inputs idle valid operation
    (by intro t h; exact reset t (by omega)) (alive 1 (by omega))
  obtain ⟨n, time, outputValid, tag, data⟩ := normalized_result (run s inputs start)
    (fun t => inputs (start + t)) (absoluteWord (signedA (inputs 0)))
    (absoluteWord (signedB (inputs 0))) prepared.1 prepared.2.1 prepared.2.2.1 prepared.2.2.2.1
    (by intro t h; apply reset; dsimp [start]; omega)
    (by intro t h; apply alive; dsimp [start]; omega)
  refine ⟨start + n, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp [start]; omega
  · dsimp [start]; omega
  · rw [run_offset]; exact outputValid
  · rw [run_offset]
    exact tag.trans (congrArg (fun m => m.2.1) prepared.2.2.2.2.2)
  · rw [run_offset, data, prepared.2.2.2.2.1,
      show (run s inputs start).r1_nreq_5Fdw = (inputs 0).nio_5Freq_5Fbits_5Fdw from
        congrArg (fun m => m.1) prepared.2.2.2.2.2,
      show (run s inputs start).r5_nisHi = signedHigh (inputs 0) from
        congrArg (fun m => m.2.2) prepared.2.2.2.2.2]
    rfl

/-- A reset edge suffices even when all data registers initially contain
    arbitrary values. -/
theorem signed_after_reset_result (s : State) (resetInput : Inputs) (inputs : Nat → Inputs)
    (resetEdge : resetInput.nreset = 1) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 4#4 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 6#4)
    (reset : ∀ t, t < 68 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 68 → (inputs t).nio_5Fkill = 0) :
    ∃ n, 66 ≤ n ∧ n ≤ 68 ∧
      (observe (run (step s resetInput) inputs n) (inputs n)).nio_5Fresp_5Fvalid = 1 ∧
      (observe (run (step s resetInput) inputs n) (inputs n)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag ∧
      (observe (run (step s resetInput) inputs n) (inputs n)).nio_5Fresp_5Fbits_5Fdata = signedSpecification (inputs 0) := by
  apply signed_accepted_result _ inputs _ valid operation reset alive
  simp [step, eval_eq_spec, evalSpec, v0, resetEdge]

#print axioms signed_after_reset_result
#print axioms signed_accepted_result
#print axioms signed_setup_run
end HierarchicalMulDiv
