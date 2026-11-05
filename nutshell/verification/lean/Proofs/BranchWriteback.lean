import Proofs.BranchPipeline
import Proofs.WritebackOrigin
namespace NutShellProofs
open nNutCore

/-- No branch register write is possible, even without assuming a commit. -/
theorem branch_writeback_disabled_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v11462 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 := by
  rcases BitVec.eq_zero_or_eq_one (v11462 (run initial inputs (t + 2)) (inputs (t + 2))) with zero | one
  · exact zero
  · have origin := next_writeback_origin _ _ _ one
    have decoded := (branch_decode_run initial inputs reset t).2 origin.1 operation matched unit
    have noWrite : v11475 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := decoded.2.2.2.2
    have write := origin.2.1
    rw [noWrite] at write
    contradiction

#print axioms branch_writeback_disabled_run
end NutShellProofs
