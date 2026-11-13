import Proofs.ArrayHold
import Std.Tactic

namespace ArrayStall
open nArrayMulDataModule

private theorem and_left (x y : BitVec 1) (h : x &&& y = 1) : x = 1 := by
  bv_decide

private theorem holding_disabled (s : State) (i : Inputs)
    (flag : (step s i).g79.r2539_nwasHoldingKnownResult = 1) :
    i.nio_5FregEnables_5F1 = 0 := by
  change (if i.nreset = 1 then v6 s i else v16462 s i) = 1 at flag
  simp only [v6, v16462, v16461, v3021] at flag
  bv_decide

/-- The exported stall check holds after every edge, from arbitrary registers.
This uses the actual output-hold theorem, independently of the arithmetic check. -/
theorem stall_check (s : State) (i later : Inputs) :
    v59797 (step s i) later ≠ 1 ∨ v59796 (step s i) later = 1 := by
  by_cases flag : (step s i).g79.r2539_nwasHoldingKnownResult = 1
  · right
    have disabled := holding_disabled s i flag
    have held := congrArg Outputs.nio_5Fresult (ArrayHold.output_hold s i i later disabled)
    change v16460 (step s i) later = v16460 s i at held
    change (if v16460 (step s i) later = (step s i).g79.r2538_npreviousResult
      then (1 : BitVec 1) else 0) = 1
    change (if v16460 (step s i) later = v16460 s i then (1 : BitVec 1) else 0) = 1
    simp only [held, if_true]
  · left
    intro enabled
    exact flag (and_left _ _ enabled)

end ArrayStall
