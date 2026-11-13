import Proofs.ArrayMatrixInput
import Proofs.ArrayMatrixArithmetic

namespace HierarchicalArray
open DesignnArrayMulDataModule.nArrayMulDataModule
open HierarchicalColumns

theorem captured_input_product (s : State) (i : Inputs) :
    BitVec.ofNat 130 (weighted 130 (capturedColumns s i)) =
      BitVec.ofInt 130 (i.nio_5Fa.toInt * i.nio_5Fb.toInt) := by
  rw [captured_matrix_sum, booth_matrix_packed, packed_input_product]

/-- Two enabled edges compute the full signed product sampled at the first
    edge, independently of initial data registers and subsequent operands. -/
theorem two_edges_product (s : State) (first second later : Inputs)
    (capture : first.nio_5FregEnables_5F0 = 1)
    (transfer : second.nio_5FregEnables_5F1 = 1) :
    (observe (step (step s first) second) later).nio_5Fresult =
      BitVec.ofInt 130 (first.nio_5Fa.toInt * first.nio_5Fb.toInt) := by
  rw [two_edges_captured_columns s first second later capture transfer,
    captured_input_product]

end HierarchicalArray
