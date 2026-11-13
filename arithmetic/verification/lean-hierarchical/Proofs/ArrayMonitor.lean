import Generated.ArrayMulDataModule
import Std.Tactic

namespace HierarchicalArray
open DesignnArrayMulDataModule.nArrayMulDataModule

/-- Expected data and validity follow the independently enabled register stages.
    This contract concerns the monitor; datapath correctness is a separate obligation. -/
def monitor (s : State) : BitVec 130 × BitVec 1 × BitVec 130 × BitVec 1 :=
  (s.g126.r2534_nexpectedFirst, s.g126.r2535_nvalidFirst,
    s.g126.r2536_nexpectedResult, s.g126.r2537_nresultKnown)

def signedProduct (i : Inputs) : BitVec 130 :=
  i.nio_5Fa.signExtend 130 * i.nio_5Fb.signExtend 130

private theorem monitor_product (s : State) (i : Inputs) :
    v5363 s i = signedProduct i := by
  unfold v5363 signedProduct
  congr 1 <;> simp only [v5359, v5358, v5357, v5362, v5361, v5360] <;> bv_decide

theorem monitor_transition (s : State) (i : Inputs) :
    monitor (step s i) =
      (if i.nio_5FregEnables_5F0 = 1 then signedProduct i else (monitor s).1,
       if i.nreset = 1 then 0 else i.nio_5FregEnables_5F0 ||| (monitor s).2.1,
       if i.nio_5FregEnables_5F1 = 1 then (monitor s).1 else (monitor s).2.2.1,
       if i.nreset = 1 then 0 else
         if i.nio_5FregEnables_5F1 = 1 then (monitor s).2.1 else (monitor s).2.2.2) := by
  simp only [monitor, step, eval_eq_spec]
  change (v5364 s i, if i.nreset = 1 then v6 s i else v5365 s i,
    v5366 s i, if i.nreset = 1 then v6 s i else v5367 s i) = _
  simp only [v5364, v5365, v5366, v5367, v6, monitor_product]
  rfl

theorem monitor_reset (s : State) (i : Inputs) (reset : i.nreset = 1) :
    (monitor (step s i)).2.1 = 0 ∧ (monitor (step s i)).2.2.2 = 0 := by
  rw [monitor_transition]
  simp only [reset, if_true, and_self]

theorem monitor_two_edges (s : State) (capture transfer : Inputs)
    (first : capture.nio_5FregEnables_5F0 = 1)
    (second : transfer.nio_5FregEnables_5F1 = 1)
    (resetFirst : capture.nreset = 0) (resetSecond : transfer.nreset = 0) :
    (monitor (step (step s capture) transfer)).2.2.1 = signedProduct capture ∧
    (monitor (step (step s capture) transfer)).2.2.2 = 1 := by
  rw [monitor_transition, monitor_transition]
  simp [first, second, resetFirst, resetSecond]
  bv_decide

end HierarchicalArray
