import Proofs.MulDivCheckedData
import Proofs.MulDivCheckedProductBits

namespace MulDivCheckedMulBridge
open nMulDivChecked
open MulDivCheckedData (product)

private theorem product_unsigned (s : State) (op : s.r11_ncontractFn = 0 ∨ s.r11_ncontractFn = 3) :
    product s = (0#64 ++ s.r13_ncontractA) * (0#64 ++ s.r14_ncontractB) := by
  rcases op with op | op <;> simp [product, op]

private theorem product_signed (s : State) (op : s.r11_ncontractFn = 1) :
    product s = (BitVec.replicate 64 (s.r13_ncontractA.extractLsb' 63 1) ++ s.r13_ncontractA) *
      (BitVec.replicate 64 (s.r14_ncontractB.extractLsb' 63 1) ++ s.r14_ncontractB) := by
  have one_and (x : BitVec 1) : 1#1 &&& x = x := by bv_decide
  simp [product, op, one_and]

private theorem product_mixed (s : State) (op : s.r11_ncontractFn = 2) :
    product s = (BitVec.replicate 64 (s.r13_ncontractA.extractLsb' 63 1) ++ s.r13_ncontractA) *
      (0#64 ++ s.r14_ncontractB) := by
  have one_and (x : BitVec 1) : 1#1 &&& x = x := by bv_decide
  simp [product, op, one_and]

/-- Each independently proved multiply specification equals the captured
source expression; no multiplication truth table is assumed. -/
theorem expected_eq_specification (s : State)
    (legal : MulDivCheckedMulSpec.Legal (MulDivCheckedHistory.captured s)) :
    MulDivCheckedData.expected s = MulDivCheckedMulSpec.specification (MulDivCheckedHistory.captured s) := by
  have range : s.r11_ncontractFn < 4#4 := legal.1
  have multiplication : s.r11_ncontractFn.extractLsb' 2 1 ≠ 1 := by bv_decide
  have cases : s.r11_ncontractFn = 0 ∨ s.r11_ncontractFn = 1 ∨ s.r11_ncontractFn = 2 ∨ s.r11_ncontractFn = 3 := by bv_decide
  simp only [MulDivCheckedData.expected, multiplication, if_false]
  rcases cases with op | op | op | op
  · rw [show MulDivCheckedMulSpec.specification (MulDivCheckedHistory.captured s) =
        (if s.r12_ncontractDw = 1 then MulDivMultiply.lowSpecification (MulDivCheckedHistory.captured s)
         else MulDivMultiply.wordSpecification (MulDivCheckedHistory.captured s)) by
          simp [MulDivCheckedMulSpec.specification, MulDivCheckedHistory.captured, op]]
    rw [MulDivMultiply.lowSpecification_eq, MulDivMultiply.wordSpecification_eq]
    simp only [MulDivCheckedData.multiplyValue, op, if_true]
    rw [product_unsigned s (Or.inl op)]
    simp only [MulDivCheckedHistory.captured]
    rw [MulDivCheckedProductBits.low, MulDivCheckedProductBits.word]
    unfold MulDivCheckedData.format
    split
    · rfl
    · have packing (x : BitVec 128) :
          BitVec.replicate 32 ((x.extractLsb' 0 64).extractLsb' 31 1) ++
            (x.extractLsb' 0 64).extractLsb' 0 32 = (x.extractLsb' 0 32).signExtend 64 := by bv_decide
      exact packing _
  all_goals
    have full : s.r12_ncontractDw = 1 := by
      have h := legal.2
      simp only [MulDivCheckedHistory.captured] at h
      bv_decide
    simp only [MulDivCheckedData.format, full, if_true, MulDivCheckedData.multiplyValue]
  · rw [product_signed s op]
    simp only [MulDivCheckedMulSpec.specification, MulDivMultiply.signedHighSpecification,
      MulDivCheckedHistory.captured, op]
    simp only [show (1 : BitVec 4) ≠ 0 by decide, show (1 : BitVec 4) ≠ 3 by decide, if_false, if_true]
    exact (MulDivCheckedProductBits.signed_high _ _).symm
  · rw [product_mixed s op]
    simp only [MulDivCheckedMulSpec.specification, MulDivMultiply.signedHighSpecification,
      MulDivCheckedHistory.captured, op]
    simp only [show (2 : BitVec 4) ≠ 0 by decide, show (2 : BitVec 4) ≠ 3 by decide,
      show (2 : BitVec 4) ≠ 1 by decide, if_false]
    exact (MulDivCheckedProductBits.mixed_high _ _).symm
  · rw [product_unsigned s (Or.inr op)]
    simp only [MulDivCheckedMulSpec.specification, MulDivMultiply.unsignedHighSpecification,
      MulDivCheckedHistory.captured, op]
    simp only [show (3 : BitVec 4) ≠ 0 by decide, if_false, if_true]
    exact (MulDivCheckedProductBits.unsigned_high _ _).symm

end MulDivCheckedMulBridge
