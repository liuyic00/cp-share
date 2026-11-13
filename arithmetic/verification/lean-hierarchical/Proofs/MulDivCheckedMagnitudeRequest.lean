import Proofs.MulDivCheckedSignedMagnitude
import Proofs.MulDivCheckedUnsignedMagnitude

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

def divisionMagnitudeA (i : Inputs) : BitVec 64 :=
  if i.nio_5Freq_5Fbits_5Ffn = 4#4 ∨ i.nio_5Freq_5Fbits_5Ffn = 6#4 then
    HierarchicalMulDiv.absoluteWord (HierarchicalMulDiv.signedA (coreInputs i))
  else HierarchicalMulDiv.unsignedOperand i.nio_5Freq_5Fbits_5Fin1 i.nio_5Freq_5Fbits_5Fdw

def divisionMagnitudeB (i : Inputs) : BitVec 64 :=
  if i.nio_5Freq_5Fbits_5Ffn = 4#4 ∨ i.nio_5Freq_5Fbits_5Ffn = 6#4 then
    HierarchicalMulDiv.absoluteWord (HierarchicalMulDiv.signedB (coreInputs i))
  else HierarchicalMulDiv.unsignedOperand i.nio_5Freq_5Fbits_5Fin2 i.nio_5Freq_5Fbits_5Fdw

def divisionRequest (i : Inputs) : Prop :=
  i.nio_5Freq_5Fbits_5Ffn = 4#4 ∨ i.nio_5Freq_5Fbits_5Ffn = 5#4 ∨
  i.nio_5Freq_5Fbits_5Ffn = 6#4 ∨ i.nio_5Freq_5Fbits_5Ffn = 7#4

theorem division_monitor_accepted (s : State) (inputs : Nat → Inputs)
    (idle : s.r0_nstate = 0) (valid : (inputs 0).nio_5Freq_5Fvalid = 1)
    (operation : divisionRequest (inputs 0))
    (reset : ∀ t, t < 68 → (inputs t).nreset = 0)
    (alive : ∀ t, t < 68 → (inputs t).nio_5Fkill = 0) :
    ∃ n, 66 ≤ n ∧ n ≤ 68 ∧
      v38 (run s inputs n) (inputs n) = 1 ∧
      v232 (run s inputs n) (inputs n) =
        magnitudeQuotient (divisionMagnitudeA (inputs 0)) (divisionMagnitudeB (inputs 0)) ∧
      v233 (run s inputs n) (inputs n) =
        magnitudeResidue (divisionMagnitudeA (inputs 0)) (divisionMagnitudeB (inputs 0)) := by
  by_cases signed : (inputs 0).nio_5Freq_5Fbits_5Ffn = 4#4 ∨
      (inputs 0).nio_5Freq_5Fbits_5Ffn = 6#4
  · simpa only [divisionMagnitudeA, divisionMagnitudeB, signed, if_true] using
      signed_monitor_accepted s inputs idle valid signed reset alive
  · have unsigned : (inputs 0).nio_5Freq_5Fbits_5Ffn = 5#4 ∨
        (inputs 0).nio_5Freq_5Fbits_5Ffn = 7#4 := by
      rcases operation with h | h | h | h
      · exact (signed (Or.inl h)).elim
      · exact Or.inl h
      · exact (signed (Or.inr h)).elim
      · exact Or.inr h
    simpa only [divisionMagnitudeA, divisionMagnitudeB, signed, if_false] using
      unsigned_monitor_accepted s inputs idle valid unsigned reset alive

end HierarchicalMulDivChecked
