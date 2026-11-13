import Proofs.RadixDivisorInvariant
import Proofs.WidenedDivisionBalance

namespace HierarchicalRadix
open DesignnRadix2Divider.nRadix2Divider

/-- Physical result slices satisfying the Euclidean identity discharge the
    widened reconstruction assertion without bit-blasting multiplication. -/
theorem nonzero_result_checks (s : State) (i : Inputs)
    (balance : (BitVec.extractLsb' 0 64 s.r2_nshiftReg).toNat * s.r5_nbReg.toNat +
      (BitVec.extractLsb' 65 64 s.r2_nshiftReg).toNat =
      (BitVec.extractLsb' 1 64 s.r6_naValx2Reg).toNat)
    (bound : (BitVec.extractLsb' 65 64 s.r2_nshiftReg).toNat < s.r5_nbReg.toNat) :
    v430 s i = 1 ∧ v431 s i = 1 := by
  have reconstruction := HierarchicalDivision.widened_balance _ _ _ _ balance
  simp only [v430, v428, v426, v425, v423, v424, v427, v429,
    v20, v26, v413, v40, v402, v418, v431]
  simp only [reconstruction, bound, if_true]
  exact ⟨trivial, trivial⟩

end HierarchicalRadix
