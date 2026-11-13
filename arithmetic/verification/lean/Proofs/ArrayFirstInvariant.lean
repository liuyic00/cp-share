import Proofs.ArrayCapture
import Proofs.ArrayContract

namespace ArrayCapture
open nArrayMulDataModule

private theorem oneBitZero (x : BitVec 1) (h : x ≠ 1) : x = 0 := by bv_decide

def FirstInvariant (s : State) : Prop :=
  s.g79.r2535_nvalidFirst = 1 → registeredRowSum s = s.g79.r2534_nexpectedFirst

theorem first_invariant_step (s : State) (i : Inputs) (invariant : FirstInvariant s) :
    FirstInvariant (step s i) := by
  intro known
  by_cases resetting : i.nreset = 1
  · have cleared := (ArrayContract.reset_unknown s i resetting).1
    rw [cleared] at known
    contradiction
  have reset : i.nreset = 0 := oneBitZero i.nreset resetting
  by_cases enabled : i.nio_5FregEnables_5F0 = 1
  · rw [capture_product s i enabled, ArrayContract.first_capture s i enabled]
    simp only [ArrayContract.specification, BitVec.signExtend, BitVec.ofInt_mul]
  · have disabled : i.nio_5FregEnables_5F0 = 0 := oneBitZero i.nio_5FregEnables_5F0 enabled
    have validHeld : (step s i).g79.r2535_nvalidFirst = s.g79.r2535_nvalidFirst := by
      change (if i.nreset = 1 then v6 s i else v16202 s i) = _
      simp [reset, v16202, disabled]
    rw [hold_sum s i disabled, ArrayContract.first_hold s i disabled]
    exact invariant (validHeld.symm.trans known)

theorem first_invariant_after_reset (s : State) (resetInput : Inputs) (reset : resetInput.nreset = 1)
    (inputs : Nat → Inputs) (n : Nat) : FirstInvariant (run (step s resetInput) inputs n) := by
  induction n with
  | zero =>
    intro known
    change (step s resetInput).g79.r2535_nvalidFirst = 1 at known
    have cleared := (ArrayContract.reset_unknown s resetInput reset).1
    rw [cleared] at known
    contradiction
  | succ n ih => exact first_invariant_step _ _ ih

end ArrayCapture
