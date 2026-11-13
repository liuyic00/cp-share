import Proofs.ArrayHold
import Proofs.ArrayMonitor

namespace HierarchicalArray
open DesignnArrayMulDataModule.nArrayMulDataModule
open HierarchicalColumns

def firstValue (s : State) (i : Inputs) : BitVec 130 :=
  BitVec.ofNat 130 (weighted 130 (stage0Input s i))

theorem first_value_input_independent (s : State) (i later : Inputs) :
    firstValue s i = firstValue s later := by rfl

theorem first_value_capture (s : State) (i later : Inputs)
    (enabled : i.nio_5FregEnables_5F0 = 1) :
    firstValue (step s i) later =
      BitVec.ofInt 130 (i.nio_5Fa.toInt * i.nio_5Fb.toInt) := by
  unfold firstValue
  rw [weighted_congr 130 _ _ (first_columns_capture s i later enabled),
    captured_input_product]

theorem first_value_hold (s : State) (i later : Inputs)
    (disabled : i.nio_5FregEnables_5F0 = 0) :
    firstValue (step s i) later = firstValue s i := by
  unfold firstValue
  rw [weighted_congr 130 _ _ (first_columns_hold s i later disabled)]

end HierarchicalArray
