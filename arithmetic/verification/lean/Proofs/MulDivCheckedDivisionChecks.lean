import Proofs.MulDivCheckedDivisionTrace
import Proofs.MulDivCheckedMetadata
import Proofs.RadixArithmeticChecks

namespace MulDivCheckedDivisionChecks
open nMulDivChecked
open MulDivCheckedMagnitude (parameters)

def quotient (s : State) : BitVec 64 :=
  if s.r16_ncontractWasNegated = 1 then s.r17_ncontractQuotient else s.r8_nremainder.extractLsb' 0 64

def residue (s : State) : BitVec 64 :=
  if s.r16_ncontractWasNegated = 1 then s.r18_ncontractResidue else s.r8_nremainder.extractLsb' 65 64

def base (s : State) (i : Inputs) : BitVec 1 :=
  ((s.r9_ncontractPending &&& (i.nio_5Fkill ^^^ 1)) &&& (observe s i).nio_5Fresp_5Fvalid) &&&
    s.r11_ncontractFn.extractLsb' 2 1

def zeroGate (s : State) (i : Inputs) : BitVec 1 :=
  (base s i &&& ((if (parameters s).2 ≠ 0 then 1 else 0) ^^^ 1)) &&& (i.nreset ^^^ 1)

def nonzeroGate (s : State) (i : Inputs) : BitVec 1 :=
  (base s i &&& (if (parameters s).2 ≠ 0 then 1 else 0)) &&& (i.nreset ^^^ 1)

theorem checks (s : State) (i : Inputs) : ((eval s i).assertions.drop 4).take 4 =
    [decide (zeroGate s i ≠ 1 ∨ (if quotient s = BitVec.allOnes 64 then (1 : BitVec 1) else 0) = 1),
     decide (zeroGate s i ≠ 1 ∨ (if residue s = (parameters s).1 then (1 : BitVec 1) else 0) = 1),
     decide (nonzeroGate s i ≠ 1 ∨ (if
       (0#1 ++ ((0#64 ++ quotient s) * (0#64 ++ (parameters s).2))) + (0#65 ++ residue s) =
       (0#65 ++ (parameters s).1) then (1 : BitVec 1) else 0) = 1),
     decide (nonzeroGate s i ≠ 1 ∨ (if (residue s).toNat < (parameters s).2.toNat then (1 : BitVec 1) else 0) = 1)] := by
  rfl

theorem source_witness (s : State) : (quotient s, residue s) = MulDivCheckedWitness.witness s := by
  unfold quotient residue MulDivCheckedWitness.witness
  split <;> apply Prod.ext <;> simp only [MulDivDivision.packed, MulDivCheckedProjection.state] <;> bv_decide

theorem from_witness (s : State) (i : Inputs) (correct : MulDivCheckedWitness.Invariant s) :
    (((eval s i).assertions.drop 4).take 4).all id = true := by
  have q := congrArg Prod.fst (source_witness s)
  have r := congrArg Prod.snd (source_witness s)
  have quotientValue := q.trans correct.1
  have residueValue := r.trans correct.2
  dsimp only [Prod.fst, Prod.snd] at quotientValue residueValue
  by_cases zero : (parameters s).2 = 0
  · have quotientZero : quotient s = BitVec.allOnes 64 := by simpa [zero] using quotientValue
    have residueZero : residue s = (parameters s).1 := by
      simpa [zero] using residueValue
    rw [checks]
    simp [quotientZero, residueZero, nonzeroGate, zero]
  · have positive : 0 < (parameters s).2.toNat := by
      have bound := (parameters s).2.isLt
      have nonzero : (parameters s).2.toNat ≠ 0 := by
        intro eq
        apply zero
        exact BitVec.eq_of_toNat_eq eq
      omega
    have quotientNat : (quotient s).toNat = (parameters s).1.toNat / (parameters s).2.toNat := by
      rw [quotientValue, if_neg zero, BitVec.toNat_ofNat]
      apply Nat.mod_eq_of_lt
      exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (parameters s).1.isLt
    have residueNat : (residue s).toNat = (parameters s).1.toNat % (parameters s).2.toNat := by
      rw [residueValue, BitVec.toNat_ofNat]
      apply Nat.mod_eq_of_lt
      exact Nat.lt_trans (Nat.mod_lt _ positive) (parameters s).2.isLt
    have identity := nRadix2Divider.widened_division_identity (quotient s) (parameters s).2
      (residue s) (parameters s).1 (by rw [quotientNat, residueNat, Nat.mul_comm, Nat.div_add_mod])
    have small : (residue s).toNat < (parameters s).2.toNat := by rw [residueNat]; exact Nat.mod_lt _ positive
    change (parameters s).2 ≠ 0#64 at zero
    rw [checks]
    simp [identity, small, zeroGate, zero]

theorem inactive (s : State) (i : Inputs)
    (disabled : ¬ (s.r9_ncontractPending = 1 ∧ s.r11_ncontractFn.extractLsb' 2 1 = 1 ∧
      (observe s i).nio_5Fresp_5Fvalid = 1)) :
    (((eval s i).assertions.drop 4).take 4).all id = true := by
  have gates : zeroGate s i = 0 ∧ nonzeroGate s i = 0 := by
    simp only [zeroGate, nonzeroGate, base]
    bv_decide
  rw [checks]
  simp [gates.1, gates.2]

theorem assertions_after_reset (initial : State) (resetInput : Inputs) (reset : resetInput.nreset = 1)
    (pins : Nat → Inputs) (n : Nat) :
    (((eval (run (step initial resetInput) pins n) (pins n)).assertions.drop 4).take 4).all id = true := by
  let s := run (step initial resetInput) pins n
  by_cases active : s.r9_ncontractPending = 1 ∧ s.r11_ncontractFn.extractLsb' 2 1 = 1 ∧
      (observe s (pins n)).nio_5Fresp_5Fvalid = 1
  · have legal := MulDivCheckedMetadata.legal_run initial resetInput reset pins n active.1
    have range : s.r11_ncontractFn < 8#4 := legal.1
    have operation : MulDivCheckedDivisionInit.Operation s := by
      unfold MulDivCheckedDivisionInit.Operation
      bv_decide
    have phases := MulDivCheckedDivisionInit.run_invariant initial resetInput reset pins n active.1 operation
    change MulDivCheckedDivisionInit.Phases s at phases
    have done : s.r0_nstate = 7 := by
      have valid := active.2.2
      rcases phases with ⟨state, _⟩ | ⟨state, _⟩ | ⟨state, _⟩ | state
      · simp [observe, eval, state] at valid
      · simp [observe, eval, state] at valid
      · simp [observe, eval, state] at valid
      · exact state
    exact from_witness s (pins n)
      (MulDivCheckedDivisionTrace.witness_after_reset initial resetInput reset pins n active.1 operation done)
  · exact inactive s (pins n) active

end MulDivCheckedDivisionChecks
