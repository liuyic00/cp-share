import Generated.ArrayMulDataModule
import Std.Tactic

/-!
The exported arithmetic monitor captures the signed product at enable 0 and
transfers it at enable 1. These theorems check that the monitor expresses the
intended two-edge contract. Actual output correctness is proved separately
in `ArrayProduct`, and all exported assertions on reset traces in
`ArrayAssertions`.
-/
namespace ArrayContract
open nArrayMulDataModule

def specification (i : Inputs) : BitVec 130 :=
  i.nio_5Fa.signExtend 130 * i.nio_5Fb.signExtend 130

private theorem captured_product (s : State) (i : Inputs) :
    v16200 s i = specification i := by
  simp only [v16200, v16196, v16195, v16194, v16199, v16198, v16197,
    specification]
  congr 1 <;> bv_decide

theorem first_capture (s : State) (i : Inputs)
    (enabled : i.nio_5FregEnables_5F0 = 1) :
    (step s i).g79.r2534_nexpectedFirst = specification i := by
  change v16201 s i = _
  simp only [v16201, enabled, if_true, captured_product]

theorem transfer (s : State) (i : Inputs)
    (enabled : i.nio_5FregEnables_5F1 = 1) :
    (step s i).g79.r2536_nexpectedResult = s.g79.r2534_nexpectedFirst := by
  change v16203 s i = _
  simp only [v16203, enabled, if_true]

theorem first_hold (s : State) (i : Inputs)
    (disabled : i.nio_5FregEnables_5F0 = 0) :
    (step s i).g79.r2534_nexpectedFirst = s.g79.r2534_nexpectedFirst := by
  change v16201 s i = _
  simp [v16201, disabled]

theorem second_hold (s : State) (i : Inputs)
    (disabled : i.nio_5FregEnables_5F1 = 0) :
    (step s i).g79.r2536_nexpectedResult = s.g79.r2536_nexpectedResult := by
  change v16203 s i = _
  simp [v16203, disabled]

theorem reset_unknown (s : State) (i : Inputs) (reset : i.nreset = 1) :
    (step s i).g79.r2535_nvalidFirst = 0 ∧
      (step s i).g79.r2537_nresultKnown = 0 := by
  change (if i.nreset = 1 then v6 s i else v16202 s i) = 0 ∧
    (if i.nreset = 1 then v6 s i else v16204 s i) = 0
  simp [reset, v6]

/-- The second edge transfers the first edge's operands, even if it also
captures new operands. No constraint is placed on the later operand pins. -/
theorem two_edges (s : State) (first second : Inputs)
    (capture : first.nio_5FregEnables_5F0 = 1)
    (move : second.nio_5FregEnables_5F1 = 1) :
    (step (step s first) second).g79.r2536_nexpectedResult = specification first := by
  rw [transfer _ _ move, first_capture _ _ capture]

theorem known_after_two_edges (s : State) (first second : Inputs)
    (capture : first.nio_5FregEnables_5F0 = 1)
    (move : second.nio_5FregEnables_5F1 = 1)
    (r0 : first.nreset = 0) (r1 : second.nreset = 0) :
    (step (step s first) second).g79.r2537_nresultKnown = 1 := by
  have zero_ne_one : (0 : BitVec 1) ≠ 1 := by decide
  change (if second.nreset = 1 then v6 _ second else v16204 _ second) = _
  simp only [r1, zero_ne_one, if_false, v16204, move, if_true]
  change (if first.nreset = 1 then v6 s first else v16202 s first) = _
  simp only [r0, zero_ne_one, if_false, v16202, capture]
  bv_decide

end ArrayContract
