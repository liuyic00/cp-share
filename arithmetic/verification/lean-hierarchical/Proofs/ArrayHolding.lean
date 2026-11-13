import Proofs.ArrayValues

namespace HierarchicalArray
open DesignnArrayMulDataModule.nArrayMulDataModule

def HoldingInvariant (s : State) : Prop :=
  ∀ i, s.g126.r2539_nwasHoldingKnownResult = 1 →
    (observe s i).nio_5Fresult = s.g126.r2538_npreviousResult

theorem previous_result_transition (s : State) (i : Inputs) :
    (step s i).g126.r2538_npreviousResult = (observe s i).nio_5Fresult := by
  simp only [step, eval_eq_spec, observe]
  rfl

theorem holding_flag_transition (s : State) (i : Inputs) :
    (step s i).g126.r2539_nwasHoldingKnownResult =
      if i.nreset = 1 then 0 else
        s.g126.r2537_nresultKnown &&& (i.nio_5FregEnables_5F1 ^^^ 1) := by
  simp only [step, eval_eq_spec]
  change (if i.nreset = 1 then v6 s i else v5373 s i) = _
  simp only [v6, v5373, v5372, v3021]
  rfl

private theorem holding_disabled (known enable : BitVec 1)
    (h : known &&& (enable ^^^ 1) = 1) : enable = 0 := by bv_decide

theorem holding_after_step (s : State) (i : Inputs) :
    HoldingInvariant (step s i) := by
  intro later active
  rw [holding_flag_transition] at active
  split at active
  · contradiction
  · have disabled := holding_disabled _ _ active
    rw [previous_result_transition, output_hold s i later disabled]

end HierarchicalArray
