import Proofs.MulDivCheckedRequest

namespace HierarchicalMulDivChecked
open DesignnMulDivChecked.nMulDivChecked

private theorem extend_signed (a : BitVec 64) :
    (BitVec.replicate 64 (BitVec.extractLsb' 63 1 a) ++ a) = BitVec.ofInt 128 a.toInt := by
  change _ = a.signExtend 128
  bv_decide

private theorem extend_unsigned (a : BitVec 64) :
    (0#64 ++ a) = BitVec.ofInt 128 (a.toNat : Int) := by
  rw [BitVec.ofInt_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_append]
  simp [Nat.mod_eq_of_lt (show a.toNat < 2^128 by have := a.isLt; omega)]

private theorem one_and (x : BitVec 1) : 1#1 &&& x = x := by bv_decide

theorem high_monitor_product (s : State) (i : Inputs)
    (operation : s.r11_ncontractFn = 1#4 ∨ s.r11_ncontractFn = 2#4 ∨ s.r11_ncontractFn = 3#4) :
    v248 s i = BitVec.ofInt 128
      ((if s.r11_ncontractFn = 3#4 then (s.r13_ncontractA.toNat : Int) else s.r13_ncontractA.toInt) *
       (if s.r11_ncontractFn = 1#4 then s.r14_ncontractB.toInt else (s.r14_ncontractB.toNat : Int))) := by
  rw [BitVec.ofInt_mul]
  unfold v248
  congr 1
  · rcases operation with h | h | h <;>
      simp [v245, v244, v241, v239, v237, v238, v194, v193, v240, h,
        one_and, extend_signed, extend_unsigned]
    all_goals change _ = s.r13_ncontractA.signExtend 128
    all_goals bv_decide
  · rcases operation with h | h | h <;>
      simp [v247, v246, v243, v237, v194, v242, h, one_and, extend_signed, extend_unsigned]
    all_goals change _ = s.r14_ncontractB.signExtend 128
    all_goals bv_decide

theorem high_monitor_specification (s : State) (i : Inputs)
    (full : s.r12_ncontractDw = 1)
    (operation : s.r11_ncontractFn = 1#4 ∨ s.r11_ncontractFn = 2#4 ∨ s.r11_ncontractFn = 3#4) :
    v258 s i = HierarchicalMulDiv.highProductSpecification (coreInputs (recordedRequest s)) := by
  have division : v198 s i = 0 := by simp only [v198]; bv_decide
  have low : v249 s i = 0 := by simp only [v249, v154]; bv_decide
  simp only [v258, full, if_true, v253, division, v252, low, v251]
  rw [HierarchicalMulDiv.high_product_specification_math]
  change BitVec.extractLsb' 64 64 (v248 s i) = BitVec.extractLsb' 64 64 _
  rw [high_monitor_product s i operation]
  rfl

private theorem low_product (a b : BitVec 64) :
    BitVec.extractLsb' 0 64 ((0#64 ++ a) * (0#64 ++ b)) = a * b := by
  change (((0#64 ++ a) * (0#64 ++ b)).setWidth 64) = _
  rw [BitVec.setWidth_mul _ _ (by decide)]
  have low (x : BitVec 64) : (0#64 ++ x).setWidth 64 = x := by bv_decide
  rw [low, low]

private theorem word_format (x : BitVec 64) :
    (BitVec.replicate 32 (BitVec.extractLsb' 31 1 x) ++ BitVec.extractLsb' 0 32 x) =
      (x.setWidth 32).signExtend 64 := by bv_decide

theorem low_monitor_specification (s : State) (i : Inputs) (operation : s.r11_ncontractFn = 0#4) :
    v258 s i = HierarchicalMulDiv.multiplicationSpecification (coreInputs (recordedRequest s)) := by
  have product : v248 s i = (0#64 ++ s.r13_ncontractA) * (0#64 ++ s.r14_ncontractB) := by
    simp [v248, v245, v244, v241, v239, v237, v238, v194, v193,
      v247, v246, v243, operation]
  have division : v198 s i = 0 := by simp [v198, operation]
  have low : v249 s i = 1 := by simp [v249, v154, operation]
  simp only [v258, v257, v256, v255, v254, v253, v252, division, low,
    v250, product, low_product, HierarchicalMulDiv.multiplicationSpecification,
    coreInputs, recordedRequest, operation]
  simp only [show (0 : BitVec 1) ≠ 1 from by decide, if_false, if_true]
  rw [word_format, BitVec.setWidth_mul _ _ (by decide)]

theorem multiplication_monitor_specification (s : State) (i : Inputs)
    (legal : s.r11_ncontractFn = 0#4 ∨
      (s.r12_ncontractDw = 1 ∧
        (s.r11_ncontractFn = 1#4 ∨ s.r11_ncontractFn = 2#4 ∨ s.r11_ncontractFn = 3#4))) :
    v258 s i = HierarchicalMulDiv.multiplicationSpecification (coreInputs (recordedRequest s)) := by
  rcases legal with low | ⟨full, high⟩
  · exact low_monitor_specification s i low
  · have nonzero : s.r11_ncontractFn ≠ 0#4 := by bv_decide
    rw [high_monitor_specification s i full high]
    simp only [HierarchicalMulDiv.multiplicationSpecification, coreInputs,
      recordedRequest, nonzero, if_false]

end HierarchicalMulDivChecked
