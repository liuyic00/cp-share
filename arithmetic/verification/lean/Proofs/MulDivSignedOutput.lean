import Proofs.MulDivSignedExecution

namespace MulDivSigned
open nMulDiv
open MulDivDivision (packed)
open MulDivOutput (metadata)
open MulDivUnsigned (format)

def selected (s : State) : BitVec 64 :=
  if s.r6_nresHi = 1 then (packed s).extractLsb' 65 64 else (packed s).extractLsb' 0 64

def completed (s : State) (i : Inputs) (negative : BitVec 1) : State :=
  if negative = 1 then step s i else s

def correctionEdges (negative : BitVec 1) : Nat := if negative = 1 then 1 else 0

theorem negate_response (s : State) (i : Inputs) (state : s.r0_nstate = 5)
    (reset : i.nreset = 0) (kill : i.nio_5Fkill = 0) :
    (step s i).r0_nstate = 7 ∧ (step s i).r6_nresHi = 0 ∧
    (packed (step s i)).extractLsb' 0 64 = -selected s ∧
    metadata (step s i) = metadata s := by
  simp only [step, eval, state, reset, kill, packed, selected, metadata, Prod.mk.injEq]
  bv_decide

/-- The optional neg_output edge restores the selected result's sign, and
preserves the captured width and response tag. -/
theorem completion_result (s : State) (i pins : Inputs) (negative : BitVec 1)
    (state : s.r0_nstate = if negative = 1 then 5 else 7)
    (reset : i.nreset = 0) (kill : i.nio_5Fkill = 0) :
    (observe (completed s i negative) pins).nio_5Fresp_5Fvalid = 1 ∧
    (observe (completed s i negative) pins).nio_5Fresp_5Fbits_5Fdata =
      format s.r1_nreq_5Fdw (if negative = 1 then -selected s else selected s) ∧
    (observe (completed s i negative) pins).nio_5Fresp_5Fbits_5Ftag = s.r2_nreq_5Ftag := by
  by_cases negate : negative = 1
  · have currentState : s.r0_nstate = 5 := by simpa only [negate, if_true] using state
    have edge := negate_response s i currentState reset kill
    have width := congrArg (fun m => m.1) edge.2.2.2
    have tag := congrArg (fun m => m.2.1) edge.2.2.2
    dsimp only [metadata] at width tag
    have output := MulDivUnsigned.observe_format (step s i) pins edge.1
    simp only [completed, negate, if_true]
    refine ⟨MulDivControl.done_valid _ _ (Or.inr edge.1), ?_, output.2.trans tag⟩
    rw [output.1, edge.2.1, width]
    simp only [show (0 : BitVec 1) ≠ 1 by decide, if_false, edge.2.2.1]
  · have currentState : s.r0_nstate = 7 := by simpa only [negate, if_false] using state
    have output := MulDivUnsigned.observe_format s pins currentState
    simp only [completed, negate, if_false]
    exact ⟨MulDivControl.done_valid _ _ (Or.inr currentState), output.1, output.2⟩

def coreResult (a d : BitVec 64) (hi negative : BitVec 1) : BitVec 64 :=
  let q := if d = 0 then BitVec.allOnes 64 else BitVec.ofNat 64 (a.toNat / d.toNat)
  let r := BitVec.ofNat 64 (a.toNat % d.toNat)
  let value := if hi = 1 then r else q
  if effectiveNegative d hi negative = 1 then -value else value

/-- The division core and optional sign correction yield the specified
response in 65 or 66 edges from a magnitude-initialized compute state. -/
theorem prepared_result_exact (s : State) (inputs : Nat → Inputs) (a d : BitVec 64)
    (state : s.r0_nstate = 3) (count : s.r3_ncount = 0)
    (divisor : s.r7_ndivisor = 0#1 ++ d) (initial : packed s = 0#65 ++ a)
    (reset : ∀ t, t < 66 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 66 → (inputs t).nio_5Fkill = 0) :
    ∃ n, n = 65 + correctionEdges (effectiveNegative d s.r5_nisHi s.r4_nneg_5Fout) ∧
      65 ≤ n ∧ n ≤ 66 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fvalid = 1 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Fdata =
        format s.r1_nreq_5Fdw (coreResult a d s.r5_nisHi s.r4_nneg_5Fout) ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Ftag = s.r2_nreq_5Ftag := by
  have control := finish65 s inputs a d state count divisor initial
    (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
  have arithmetic := MulDivUnsigned.magnitudes s inputs a d state count divisor initial
    (fun t h => reset t (by omega)) (fun t h => kill t (by omega))
  let negative := effectiveNegative d s.r5_nisHi s.r4_nneg_5Fout
  let extra := correctionEdges negative
  have extraBound : extra ≤ 1 := by unfold extra correctionEdges; split <;> decide
  have response := completion_result (run s inputs 65) (inputs 65) (inputs (65 + extra))
    negative control.1 (reset 65 (by decide)) (kill 65 (by decide))
  have finalState : completed (run s inputs 65) (inputs 65) negative = run s inputs (65 + extra) := by
    unfold completed extra correctionEdges
    split <;> rfl
  rw [finalState] at response
  have width := congrArg (fun m => m.1) control.2.2
  have tag := congrArg (fun m => m.2.1) control.2.2
  dsimp only [metadata] at width tag
  refine ⟨65 + extra, rfl, by omega, by omega, response.1, ?_, response.2.2.trans tag⟩
  rw [response.2.1, width]
  simp only [selected, control.2.1, arithmetic.1, arithmetic.2, coreResult, negative]

theorem prepared_result (s : State) (inputs : Nat → Inputs) (a d : BitVec 64)
    (state : s.r0_nstate = 3) (count : s.r3_ncount = 0)
    (divisor : s.r7_ndivisor = 0#1 ++ d) (initial : packed s = 0#65 ++ a)
    (reset : ∀ t, t < 66 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 66 → (inputs t).nio_5Fkill = 0) :
    ∃ n, 65 ≤ n ∧ n ≤ 66 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fvalid = 1 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Fdata =
        format s.r1_nreq_5Fdw (coreResult a d s.r5_nisHi s.r4_nneg_5Fout) ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Ftag = s.r2_nreq_5Ftag := by
  obtain ⟨n, _, low, high, result⟩ := prepared_result_exact s inputs a d state count divisor initial reset kill
  exact ⟨n, low, high, result⟩

def setupEdges (i : Inputs) : Nat := if needsNegation i then 2 else 1

theorem prepared_reached (s : State) (inputs : Nat → Inputs) :
    prepared s (inputs 0) (inputs 1) = run s inputs (setupEdges (inputs 0)) := by
  unfold prepared setupEdges
  split <;> rfl

theorem run_add (s : State) (inputs : Nat → Inputs) (k n : Nat) :
    run s inputs (k + n) = run (run s inputs k) (fun t => inputs (k + t)) n := by
  induction n with
  | zero => simp [run]
  | succ n ih =>
    rw [Nat.add_succ, run, ih, run]

def specification (i : Inputs) : BitVec 64 :=
  format i.nio_5Freq_5Fbits_5Fdw
    (coreResult (magnitude (operand i i.nio_5Freq_5Fbits_5Fin1))
      (magnitude (operand i i.nio_5Freq_5Fbits_5Fin2))
      (if i.nio_5Freq_5Fbits_5Ffn = 6 then 1 else 0) (outputNegative i))

/-- Exact total edges, including acceptance, input normalization, 65 division
iterations, and the optional output-sign correction. -/
def acceptedEdges (i : Inputs) : Nat :=
  setupEdges i + 65 + correctionEdges
    (effectiveNegative (magnitude (operand i i.nio_5Freq_5Fbits_5Fin2))
      (if i.nio_5Freq_5Fbits_5Ffn = 6 then 1 else 0) (outputNegative i))

/-- All signed DIV/REM and DIVW/REMW inputs, including zero divisors and signed
overflow. Acceptance plus optional sign stages takes 66 through 68 edges;
only the first request must be valid, and later input pins are unrestricted. -/
theorem accepted_result_exact (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 4 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 6)
    (reset : ∀ t, t < 68 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 68 → (inputs t).nio_5Fkill = 0) :
    ∃ n, n = acceptedEdges (inputs 0) ∧ 66 ≤ n ∧ n ≤ 68 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fvalid = 1 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Fdata = specification (inputs 0) ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag := by
  have prep := preparation s (inputs 0) (inputs 1) idle valid
    (reset 0 (by decide)) (reset 1 (by decide)) (kill 1 (by decide)) operation
  let k := setupEdges (inputs 0)
  have kBound : 1 ≤ k ∧ k ≤ 2 := by unfold k setupEdges; split <;> decide
  let future := fun t => inputs (k + t)
  obtain ⟨n, exactCycle, low, high, response, data, tag⟩ := prepared_result_exact
    (prepared s (inputs 0) (inputs 1)) future
    (magnitude (operand (inputs 0) (inputs 0).nio_5Freq_5Fbits_5Fin1))
    (magnitude (operand (inputs 0) (inputs 0).nio_5Freq_5Fbits_5Fin2))
    prep.1 prep.2.1 prep.2.2.1 prep.2.2.2.1
    (fun t h => reset (k + t) (by omega)) (fun t h => kill (k + t) (by omega))
  have combined : run (prepared s (inputs 0) (inputs 1)) future n = run s inputs (k + n) := by
    rw [prepared_reached]
    exact (run_add s inputs k n).symm
  rw [combined] at response data tag
  have captureMeta := prep.2.2.2.2.2
  have width := congrArg (fun m => m.1) captureMeta
  have originalTag := congrArg (fun m => m.2.1) captureMeta
  have selection := congrArg (fun m => m.2.2) captureMeta
  dsimp only [metadata] at width originalTag selection
  have total : k + n = acceptedEdges (inputs 0) := by
    rw [exactCycle, selection, prep.2.2.2.2.1]
    simp only [acceptedEdges, k, Nat.add_assoc]
  refine ⟨k + n, total, by omega, by omega, response, ?_, tag.trans originalTag⟩
  rw [data, width, selection, prep.2.2.2.2.1]
  rfl

theorem accepted_result (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 4 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 6)
    (reset : ∀ t, t < 68 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 68 → (inputs t).nio_5Fkill = 0) :
    ∃ n, 66 ≤ n ∧ n ≤ 68 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fvalid = 1 ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Fdata = specification (inputs 0) ∧
      (observe (run s inputs n) (inputs n)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag := by
  obtain ⟨n, _, low, high, result⟩ := accepted_result_exact s inputs idle valid operation reset kill
  exact ⟨n, low, high, result⟩

theorem after_reset_result (initial : State) (resetInput : Inputs)
    (resetEdge : resetInput.nreset = 1) (inputs : Nat → Inputs)
    (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : (inputs 0).nio_5Freq_5Fbits_5Ffn = 4 ∨ (inputs 0).nio_5Freq_5Fbits_5Ffn = 6)
    (reset : ∀ t, t < 68 → (inputs t).nreset = 0)
    (kill : ∀ t, t < 68 → (inputs t).nio_5Fkill = 0) :
    ∃ n, 66 ≤ n ∧ n ≤ 68 ∧
      (observe (run (step initial resetInput) inputs n) (inputs n)).nio_5Fresp_5Fvalid = 1 ∧
      (observe (run (step initial resetInput) inputs n) (inputs n)).nio_5Fresp_5Fbits_5Fdata = specification (inputs 0) ∧
      (observe (run (step initial resetInput) inputs n) (inputs n)).nio_5Fresp_5Fbits_5Ftag = (inputs 0).nio_5Freq_5Fbits_5Ftag := by
  exact accepted_result _ inputs (MulDivControl.reset_ready initial resetInput resetEdge)
    valid operation reset kill

end MulDivSigned
