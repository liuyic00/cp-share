import Proofs.MulDivCheckedData
import Proofs.MulDivCheckedSignedTiming
import Proofs.MulDivCheckedUnsignedTiming

namespace MulDivCheckedDivisionOutput
open nMulDivChecked
open MulDivCheckedDivisionInit (Operation)
open MulDivCheckedLatency (outputNegative)
open MulDivCheckedDivisionChecks (quotient residue)
set_option maxHeartbeats 2000000

def hi (s : State) : BitVec 1 := s.r11_ncontractFn.extractLsb' 1 1

def selected (s : State) : BitVec 64 := if hi s = 1 then residue s else quotient s

def expected (s : State) : BitVec 64 :=
  let value := if outputNegative s = 1 then 0 - selected s else selected s
  if s.r12_ncontractDw = 1 then value else
    BitVec.replicate 32 (value.extractLsb' 31 1) ++ value.extractLsb' 0 32

def SignInvariant (s : State) : Prop := s.r9_ncontractPending = 1 → Operation s →
  (s.r0_nstate = 3 → s.r3_ncount = 64 → s.r4_nneg_5Fout = outputNegative s) ∧
  (s.r0_nstate = 5 → outputNegative s = 1)

theorem sign_invariant (s : State) (signed : MulDivCheckedSignedTiming.Invariant s)
    (unsigned : MulDivCheckedUnsignedTiming.Invariant s) : SignInvariant s := by
  intro pending operation
  by_cases signedOp : s.r11_ncontractFn = 4 ∨ s.r11_ncontractFn = 6
  · have phases := signed pending signedOp
    constructor
    · intro state count
      rcases phases with ⟨st, _, _, ct, _⟩ | ⟨st, ct, _⟩ | ⟨st, _, _, _, flag⟩ | ⟨st, _⟩ | ⟨st, _⟩
      all_goals first | exact flag | (simp_all)
    · intro state
      rcases phases with ⟨st, _⟩ | ⟨st, _⟩ | ⟨st, _⟩ | ⟨st, _, flag⟩ | ⟨st, _⟩
      all_goals first | exact flag | (simp_all)
  · have unsignedOp : s.r11_ncontractFn = 5 ∨ s.r11_ncontractFn = 7 := by
      simp only [Operation] at operation
      bv_decide
    have phases := unsigned pending unsignedOp
    have negative : outputNegative s = 0 := by
      rcases unsignedOp with op | op <;>
        simp [outputNegative, MulDivCheckedLatency.negative, MulDivCheckedLatency.signedBit, op]
    constructor
    · intro state count
      rcases phases with ⟨st, _, _, flag⟩ | ⟨st, _⟩
      · exact flag.trans negative.symm
      · simp_all
    · intro state
      rcases phases with ⟨st, _⟩ | ⟨st, _⟩ <;> simp_all

def ResultRelation (s : State) : Prop :=
  (s.r6_nresHi = hi s ∧ s.r16_ncontractWasNegated = 0 ∧ outputNegative s = 0) ∨
  (s.r6_nresHi = 0 ∧ s.r16_ncontractWasNegated = 1 ∧ outputNegative s = 1 ∧
    s.r8_nremainder.extractLsb' 0 64 = 0 - selected s)

def Invariant (s : State) : Prop := s.r9_ncontractPending = 1 → Operation s →
  s.r5_nisHi = hi s ∧
  (s.r0_nstate = 5 → s.r6_nresHi = hi s ∧ s.r16_ncontractWasNegated = 0 ∧ outputNegative s = 1) ∧
  (s.r0_nstate = 7 → ResultRelation s)

theorem reset_invariant (s : State) (i : Inputs) (reset : i.nreset = 1) :
    Invariant (step s i) := by simp [Invariant, step, eval, reset]

theorem step_invariant (s : State) (i : Inputs) (previous : Invariant s)
    (signs : SignInvariant s) (initialization : MulDivCheckedDivisionInit.Invariant s) :
    Invariant (step s i) := by
  intro pending operation
  by_cases idle : s.r0_nstate = 0
  · simp only [Invariant, Operation, hi, ResultRelation, selected, quotient, residue,
      outputNegative, MulDivCheckedLatency.magnitude, MulDivCheckedLatency.negative,
      MulDivCheckedLatency.operand, MulDivCheckedLatency.signedBit, step, eval, idle] at *
    bv_decide
  · have oldPending : s.r9_ncontractPending = 1 := by
      simp only [step, eval] at pending
      bv_decide
    have oldOperation : Operation s := by
      simp only [Operation, step, eval] at operation ⊢
      bv_decide
    have oldCorrect := previous oldPending oldOperation
    have oldSigns := signs oldPending oldOperation
    have phases := initialization oldPending oldOperation
    rcases phases with ⟨state, facts⟩ | ⟨state, facts⟩ | ⟨state, facts⟩ | state <;>
      simp only [MulDivCheckedDivisionInit.Initialized, Invariant, Operation, hi, ResultRelation, selected, quotient, residue,
        outputNegative, MulDivCheckedLatency.magnitude, MulDivCheckedLatency.negative,
        MulDivCheckedLatency.operand, MulDivCheckedLatency.signedBit, step, eval, state] at * <;>
      bv_decide

theorem run_invariant (initial : State) (resetInput : Inputs) (reset : resetInput.nreset = 1)
    (pins : Nat → Inputs) (n : Nat) : Invariant (run (step initial resetInput) pins n) := by
  induction n with
  | zero => exact reset_invariant initial resetInput reset
  | succ n ih =>
    exact step_invariant _ _ ih
      (sign_invariant _ (MulDivCheckedSignedTiming.run_invariant initial resetInput reset pins n)
        (MulDivCheckedUnsignedTiming.run_invariant initial resetInput reset pins n))
      (MulDivCheckedDivisionInit.run_invariant initial resetInput reset pins n)

theorem output_correct (s : State) (i : Inputs) (state : s.r0_nstate = 7)
    (relation : ResultRelation s) (width : s.r1_nreq_5Fdw = s.r12_ncontractDw) :
    (observe s i).nio_5Fresp_5Fbits_5Fdata = expected s := by
  simp only [ResultRelation, expected, selected, hi, quotient, residue] at relation ⊢
  simp only [observe, eval, state]
  bv_decide

theorem expected_agrees (s : State) (operation : Operation s) :
    expected s = MulDivCheckedData.expected s := by
  have division : s.r11_ncontractFn.extractLsb' 2 1 = 1 := by
    simp only [Operation] at operation
    bv_decide
  simp only [MulDivCheckedData.expected, division, if_true]
  rfl

theorem data_assertion_after_reset (initial : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (pins : Nat → Inputs) (n : Nat)
    (operation : Operation (run (step initial resetInput) pins n)) :
    (eval (run (step initial resetInput) pins n) (pins n)).assertions[3]! = true := by
  let s := run (step initial resetInput) pins n
  by_cases active : s.r9_ncontractPending = 1 ∧ (observe s (pins n)).nio_5Fresp_5Fvalid = 1
  · have phases := MulDivCheckedDivisionInit.run_invariant initial resetInput reset pins n active.1 operation
    change MulDivCheckedDivisionInit.Phases s at phases
    have done : s.r0_nstate = 7 := by
      have valid := active.2
      rcases phases with ⟨st, _⟩ | ⟨st, _⟩ | ⟨st, _⟩ | st
      · simp [observe, eval, st] at valid
      · simp [observe, eval, st] at valid
      · simp [observe, eval, st] at valid
      · exact st
    have relation := (run_invariant initial resetInput reset pins n active.1 operation).2.2 done
    have width := (MulDivCheckedMetadata.run_invariant initial resetInput reset pins n active.1).2
    apply MulDivCheckedData.of_correct
    rw [← expected_agrees s operation]
    exact output_correct s (pins n) done relation width
  · exact MulDivCheckedData.inactive s (pins n) active

end MulDivCheckedDivisionOutput
