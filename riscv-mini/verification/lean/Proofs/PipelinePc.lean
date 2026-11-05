import Proofs.FetchControl
import Proofs.FetchPcArithmetic
import Proofs.PcBridge
import Proofs.PcSuccessorCoverage
namespace RiscvMiniProofs
open nCoreSoc

-- The oldest pending PC, accounting for the reset startup fetch at 0x1fc.
def frontPc (s : State) : BitVec 32 :=
  if s.g4.r143_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG = 0 then
    s.g3.r124_ndut_5Fdpath_5Ffe_5Freg_5Fpc
  else BitVec.extractLsb' 0 32 s.g4.r137_ndut_5Fdpath_5Fpc +
    (if s.g4.r136_ndut_5Fdpath_5Fstarted = 1 then 4 else 0)

structure PipelinePc (s : State) : Prop where
  writeback : ValidWritebackPcAgreement s
  ahead : s.g4.r143_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG = 0 →
    BitVec.extractLsb' 0 32 s.g4.r137_ndut_5Fdpath_5Fpc =
      s.g3.r124_ndut_5Fdpath_5Ffe_5Freg_5Fpc + 4
  frontier : frontPc s =
    if s.g4.r144_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG_5F1 = 0 then writebackNextPc s
    else s.g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc

theorem pipeline_pc_reset (s : State) (i : Inputs) (reset : i.nreset = 1) :
    PipelinePc (step s i) := by
  constructor
  · exact valid_writeback_pc_reset s i reset
  · intro valid
    change v8565 s i = 0 at valid
    simp [v8565, v1, v0, reset, v512] at valid
  · change (if v8565 s i = 0 then v7771 s i
      else BitVec.extractLsb' 0 32 (v8508 s i) + (if v1 s i = 1 then 4 else 0)) =
      if v8567 s i = 0 then writebackNextPc (step s i) else v6936 s i
    simp [v8565, v8567, v8508, v6936, v956, v955, v6476, v8478,
      v1, v0, v512, reset]

theorem pipeline_writeback_pc_step (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) (agree : RegisterAgreement (run initial inputs t))
    (pipeline : PipelinePc (run initial inputs t)) :
    ValidWritebackPcAgreement (run initial inputs (t+1)) := by
  apply (valid_writeback_pc_step_iff _ _ (reset.2.2 t ht) (env t)).mpr
  intro valid
  have frontier := pipeline.frontier
  simp only [frontPc, valid, ↓reduceIte] at frontier
  have next := reference_pc_step_reachable initial inputs cycles reset env t ht agree pipeline.writeback
  simp only [run] at next
  rw [next]
  simpa only [commit_iff_valid_writeback _ _ (reset.2.2 t ht)] using frontier

theorem pipeline_ahead_step (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i)
    (noReturn : s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst ≠ 268435571)
    (valid : (step s i).g4.r143_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG = 0) :
    BitVec.extractLsb' 0 32 (step s i).g4.r137_ndut_5Fdpath_5Fpc =
      (step s i).g3.r124_ndut_5Fdpath_5Ffe_5Freg_5Fpc + 4 := by
  have transfer := fetch_transfer_step s i reset env noReturn
  rw [transfer.execute_cancel] at valid
  have cancelled := BitVec.or_eq_zero_iff.mp valid
  have control := (BitVec.or_eq_zero_iff.mp cancelled.1).2
  rw [fetch_cancel_pc_select] at control
  have select : v8473 s i = 0 := by
    split at control
    · assumption
    · contradiction
  have check : v8475 s i = 0 := by
    simp [v8475, v8474, v42, select, cancelled.2]
  rw [fetch_pc_low32_step s i reset env noReturn, transfer.execute_pc]
  simp [check, select]

#print axioms pipeline_ahead_step
#print axioms pipeline_writeback_pc_step
#print axioms pipeline_pc_reset
end RiscvMiniProofs
