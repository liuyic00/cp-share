import Proofs.ArrayPaddingRegisters

namespace ArrayCapture
open nArrayMulDataModule

private theorem oneBitZero (x : BitVec 1) (h : x ≠ 1) : x = 0 := by bv_decide

def KnownPadding (s : State) : Prop := s.g79.r2535_nvalidFirst = 1 → PaddingInvariant s

theorem known_padding_step (s : State) (i : Inputs) (invariant : KnownPadding s) :
    KnownPadding (step s i) := by
  intro known
  by_cases resetting : i.nreset = 1
  · have cleared := (ArrayContract.reset_unknown s i resetting).1
    rw [cleared] at known
    contradiction
  have reset : i.nreset = 0 := oneBitZero i.nreset resetting
  by_cases enabled : i.nio_5FregEnables_5F0 = 1
  · exact padding_capture s i enabled
  · have disabled : i.nio_5FregEnables_5F0 = 0 := oneBitZero i.nio_5FregEnables_5F0 enabled
    have validHeld : (step s i).g79.r2535_nvalidFirst = s.g79.r2535_nvalidFirst := by
      change (if i.nreset = 1 then v6 s i else v16202 s i) = _
      simp [reset, v16202, disabled]
    exact (padding_hold s i disabled).mpr (invariant (validHeld.symm.trans known))

theorem known_padding_after_reset (s : State) (resetInput : Inputs) (reset : resetInput.nreset = 1)
    (inputs : Nat → Inputs) (n : Nat) : KnownPadding (run (step s resetInput) inputs n) := by
  induction n with
  | zero =>
    intro known
    change (step s resetInput).g79.r2535_nvalidFirst = 1 at known
    have cleared := (ArrayContract.reset_unknown s resetInput reset).1
    rw [cleared] at known
    contradiction
  | succ n ih => exact known_padding_step _ _ ih

/-- All first-stage arithmetic and sign-padding obligations hold whenever
its monitor says the captured product is valid, on an arbitrary reset trace. -/
theorem first_stage_after_reset (s : State) (resetInput : Inputs) (reset : resetInput.nreset = 1)
    (inputs : Nat → Inputs) (n : Nat)
    (known : (run (step s resetInput) inputs n).g79.r2535_nvalidFirst = 1) :
    registeredRowSum (run (step s resetInput) inputs n) =
      (run (step s resetInput) inputs n).g79.r2534_nexpectedFirst ∧
    PaddingInvariant (run (step s resetInput) inputs n) :=
  ⟨first_invariant_after_reset s resetInput reset inputs n known,
    known_padding_after_reset s resetInput reset inputs n known⟩

end ArrayCapture
