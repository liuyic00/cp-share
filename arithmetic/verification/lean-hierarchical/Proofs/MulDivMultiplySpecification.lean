import Proofs.MulDivMultiplicationContract

namespace HierarchicalMulDiv
open DesignnMulDiv.nMulDiv

theorem signed_operand_value (a : BitVec 64) :
    a.toInt = (a.toNat : Int) - (if operandSign a = 1#1 then 2 ^ 64 else 0) := by
  rw [BitVec.toInt_eq_toNat_cond]
  have width := a.isLt
  by_cases negative : operandSign a = 1#1
  · have top := congrArg BitVec.toNat negative
    simp [operandSign, Nat.shiftRight_eq_div_pow] at top
    simp only [negative, if_pos]
    split <;> omega
  · have zero : operandSign a = 0#1 := by bv_decide
    have top := congrArg BitVec.toNat zero
    simp [operandSign, Nat.shiftRight_eq_div_pow] at top
    simp only [negative, if_false]
    split <;> omega

theorem extended_operand_value (a : BitVec 64) :
    (operandSign a ++ a).toInt = a.toInt := by
  have extension : operandSign a ++ a = a.signExtend 65 := by
    unfold operandSign
    bv_decide
  rw [extension, BitVec.toInt_signExtend_of_le (by omega)]

/-- High-product specifications use signed operands for MULH, a signed left
    operand for MULHSU, and unsigned operands for MULHU. -/
theorem high_product_specification_math (i : Inputs) :
    highProductSpecification i = BitVec.extractLsb' 64 64 (BitVec.ofInt 128
      ((if i.nio_5Freq_5Fbits_5Ffn = 3#4 then (i.nio_5Freq_5Fbits_5Fin1.toNat : Int)
        else i.nio_5Freq_5Fbits_5Fin1.toInt) *
       (if i.nio_5Freq_5Fbits_5Ffn = 1#4 then i.nio_5Freq_5Fbits_5Fin2.toInt
        else (i.nio_5Freq_5Fbits_5Fin2.toNat : Int)))) := by
  have lhs : (i.nio_5Freq_5Fbits_5Fin1.toNat : Int) -
      (if (if i.nio_5Freq_5Fbits_5Ffn = 3#4 then 0#1 else operandSign i.nio_5Freq_5Fbits_5Fin1) = 1#1
        then 2 ^ 64 else 0) =
      (if i.nio_5Freq_5Fbits_5Ffn = 3#4 then (i.nio_5Freq_5Fbits_5Fin1.toNat : Int)
        else i.nio_5Freq_5Fbits_5Fin1.toInt) := by
    split
    · simp
    · exact (signed_operand_value _).symm
  have rhs : ((if i.nio_5Freq_5Fbits_5Ffn = 1#4 then operandSign i.nio_5Freq_5Fbits_5Fin2 else 0#1) ++
      i.nio_5Freq_5Fbits_5Fin2).toInt =
      (if i.nio_5Freq_5Fbits_5Ffn = 1#4 then i.nio_5Freq_5Fbits_5Fin2.toInt
        else (i.nio_5Freq_5Fbits_5Fin2.toNat : Int)) := by
    split
    · exact extended_operand_value _
    · rw [BitVec.toInt_append]; simp
  unfold highProductSpecification productBits
  rw [lhs, rhs]

#print axioms high_product_specification_math
end HierarchicalMulDiv
