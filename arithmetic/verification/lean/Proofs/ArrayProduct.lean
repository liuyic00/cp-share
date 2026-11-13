import Proofs.ArrayTreeInputRows
import Proofs.ArrayPaddingInvariant
import Proofs.ArrayHold

namespace ArrayProduct
open nArrayMulDataModule
open ArrayCapture

/-- Two enabled pipeline edges compute the signed product of the operands
at the first edge, independently of later input pins and initial registers. -/
theorem two_edges (s : State) (first second after : Inputs)
    (capture : first.nio_5FregEnables_5F0 = 1)
    (move : second.nio_5FregEnables_5F1 = 1) :
    (observe (step (step s first) second) after).nio_5Fresult =
      BitVec.ofInt 130 (first.nio_5Fa.toInt * first.nio_5Fb.toInt) := by
  rw [ArrayTreeInput.output_from_first_stage _ second after move
    (padding_capture s first capture), capture_product s first capture]

/-- The actual arithmetic result and its validity monitor agree after the
specified two edges; both first-stage enables may be asserted together. -/
theorem valid_product_after_two_edges (s : State) (first second after : Inputs)
    (capture : first.nio_5FregEnables_5F0 = 1)
    (move : second.nio_5FregEnables_5F1 = 1)
    (r0 : first.nreset = 0) (r1 : second.nreset = 0) :
    (step (step s first) second).g79.r2537_nresultKnown = 1 ∧
    (observe (step (step s first) second) after).nio_5Fresult =
      BitVec.ofInt 130 (first.nio_5Fa.toInt * first.nio_5Fb.toInt) :=
  ⟨ArrayContract.known_after_two_edges s first second capture move r0 r1,
    two_edges s first second after capture move⟩

private theorem oneBitZero (x : BitVec 1) (h : x ≠ 1) : x = 0 := by bv_decide

def ResultInvariant (s : State) : Prop :=
  ∀ later : Inputs, s.g79.r2537_nresultKnown = 1 →
    (observe s later).nio_5Fresult = s.g79.r2536_nexpectedResult

def PipelineInvariant (s : State) : Prop :=
  FirstInvariant s ∧ KnownPadding s ∧ ResultInvariant s

theorem invariant_step (s : State) (i : Inputs) (invariant : PipelineInvariant s) :
    PipelineInvariant (step s i) := by
  refine ⟨first_invariant_step s i invariant.1, known_padding_step s i invariant.2.1, ?_⟩
  intro later known
  by_cases resetting : i.nreset = 1
  · have cleared := (ArrayContract.reset_unknown s i resetting).2
    rw [cleared] at known
    contradiction
  have reset : i.nreset = 0 := oneBitZero i.nreset resetting
  by_cases enabled : i.nio_5FregEnables_5F1 = 1
  · have valid : s.g79.r2535_nvalidFirst = 1 := by
      change (if i.nreset = 1 then v6 s i else v16204 s i) = 1 at known
      simpa only [reset, show (0 : BitVec 1) ≠ 1 from by decide, if_false,
        v16204, enabled, if_true] using known
    rw [ArrayTreeInput.output_from_first_stage s i later enabled (invariant.2.1 valid),
      invariant.1 valid, ArrayContract.transfer s i enabled]
  · have disabled : i.nio_5FregEnables_5F1 = 0 := oneBitZero i.nio_5FregEnables_5F1 enabled
    have heldKnown : s.g79.r2537_nresultKnown = 1 := by
      change (if i.nreset = 1 then v6 s i else v16204 s i) = 1 at known
      simpa only [reset, disabled, show (0 : BitVec 1) ≠ 1 from by decide,
        if_false, v16204] using known
    have held := congrArg Outputs.nio_5Fresult (ArrayHold.output_hold s i i later disabled)
    rw [held, invariant.2.2 i heldKnown, ArrayContract.second_hold s i disabled]

theorem invariant_after_reset (s : State) (resetInput : Inputs) (reset : resetInput.nreset = 1)
    (inputs : Nat → Inputs) (n : Nat) : PipelineInvariant (run (step s resetInput) inputs n) := by
  induction n with
  | zero =>
    have cleared := ArrayContract.reset_unknown s resetInput reset
    refine ⟨?_, ?_, ?_⟩
    · intro known
      change (step s resetInput).g79.r2535_nvalidFirst = 1 at known
      rw [cleared.1] at known
      contradiction
    · intro known
      change (step s resetInput).g79.r2535_nvalidFirst = 1 at known
      rw [cleared.1] at known
      contradiction
    · intro later known
      change (step s resetInput).g79.r2537_nresultKnown = 1 at known
      rw [cleared.2] at known
      contradiction
  | succ n ih => exact invariant_step _ _ ih

end ArrayProduct
