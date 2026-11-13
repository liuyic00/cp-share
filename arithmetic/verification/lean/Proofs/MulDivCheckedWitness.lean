import Proofs.MulDivCheckedMagnitude

namespace MulDivCheckedWitness
open nMulDivChecked
open MulDivCheckedMagnitude (parameters Correct)

def witness (s : State) : BitVec 64 × BitVec 64 :=
  if s.r16_ncontractWasNegated = 1 then (s.r17_ncontractQuotient, s.r18_ncontractResidue)
  else ((MulDivDivision.packed (MulDivCheckedProjection.state s)).extractLsb' 0 64,
    (MulDivDivision.packed (MulDivCheckedProjection.state s)).extractLsb' 65 64)

def Invariant (s : State) : Prop :=
  (witness s).1 = (if (parameters s).2 = 0 then BitVec.allOnes 64 else
    BitVec.ofNat 64 ((parameters s).1.toNat / (parameters s).2.toNat)) ∧
  (witness s).2 = BitVec.ofNat 64 ((parameters s).1.toNat % (parameters s).2.toNat)

theorem from_raw (s : State) (flag : s.r16_ncontractWasNegated = 0)
    (correct : Correct (MulDivCheckedProjection.state s) (parameters s).1 (parameters s).2) :
    Invariant s := by
  simpa [Invariant, witness, flag, Correct] using correct

theorem capture (s : State) (i : Inputs) (state : s.r0_nstate = 5) (reset : i.nreset = 0) :
    witness (step s i) =
      ((MulDivDivision.packed (MulDivCheckedProjection.state s)).extractLsb' 0 64,
       (MulDivDivision.packed (MulDivCheckedProjection.state s)).extractLsb' 65 64) := by
  have flag : (step s i).r16_ncontractWasNegated = 1 := by
    simp only [step, eval, state, reset]
    bv_decide
  simp only [witness, flag, if_true]
  apply Prod.ext <;>
    simp only [step, eval, state, reset, MulDivDivision.packed, MulDivCheckedProjection.state] <;> bv_decide

theorem negation_preserves (s : State) (i : Inputs) (state : s.r0_nstate = 5) (reset : i.nreset = 0)
    (correct : Correct (MulDivCheckedProjection.state s) (parameters s).1 (parameters s).2) :
    Invariant (step s i) := by
  unfold Invariant
  rw [capture s i state reset, MulDivCheckedMagnitude.parameters_hold s i (by rw [state]; decide)]
  exact correct

theorem hold (s : State) (i : Inputs) (state : s.r0_nstate = 7) (reset : i.nreset = 0) :
    witness (step s i) = witness s := by
  have flag : (step s i).r16_ncontractWasNegated = s.r16_ncontractWasNegated := by
    simp only [step, eval, state, reset]
    bv_decide
  simp only [witness, flag]
  split <;> apply Prod.ext <;>
    simp only [step, eval, state, reset, MulDivDivision.packed, MulDivCheckedProjection.state] <;> bv_decide

theorem done_preserves (s : State) (i : Inputs) (state : s.r0_nstate = 7) (reset : i.nreset = 0)
    (correct : Invariant s) : Invariant (step s i) := by
  unfold Invariant
  rw [hold s i state reset, MulDivCheckedMagnitude.parameters_hold s i (by rw [state]; decide)]
  exact correct

end MulDivCheckedWitness
