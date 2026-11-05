import Proofs.PipelinePc
import Proofs.RedirectTransfer
namespace RiscvMiniProofs
open nCoreSoc

theorem started_zero_of_valid_step (s : State) (i : Inputs)
    (valid : (step s i).g4.r143_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG = 0) :
    (step s i).g4.r136_ndut_5Fdpath_5Fstarted = 0 := by
  rcases BitVec.eq_zero_or_eq_one i.nreset with no | yes
  · exact no
  · change v8565 s i = 0 at valid
    simp [v8565, v1, v0, yes, v512] at valid

theorem started_zero_of_valid_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (t : Nat) (ht : cycles ≤ t)
    (valid : (run initial inputs t).g4.r143_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG = 0) :
    (run initial inputs t).g4.r136_ndut_5Fdpath_5Fstarted = 0 := by
  cases t with
  | zero => have := reset.1; omega
  | succ n => exact started_zero_of_valid_step _ _ valid

theorem pipeline_frontier_step (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i)
    (noReturn : s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst ≠ 268435571)
    (bubbles : BubbleAlignment s)
    (started : s.g4.r143_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG = 0 →
      s.g4.r136_ndut_5Fdpath_5Fstarted = 0)
    (pipeline : PipelinePc s)
    (reference : (step s i).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      if s.g4.r144_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG_5F1 = 0 then writebackNextPc s
      else s.g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc) :
    frontPc (step s i) =
      if (step s i).g4.r144_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG_5F1 = 0 then
        writebackNextPc (step s i)
      else (step s i).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc := by
  have transfer := fetch_transfer_step s i reset env noReturn
  have execute := execute_transfer_step s i reset env
  have fetch := fetch_pc_low32_step s i reset env noReturn
  simp only [frontPc, transfer.started, transfer.execute_pc, transfer.execute_cancel,
    transfer.writeback_cancel, BitVec.reduceEq, ↓reduceIte]
  rcases BitVec.eq_zero_or_eq_one s.g4.r143_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG with valid | bubble
  · simp only [valid, writebackNextPc, transfer.check, execute.pc]
    rcases BitVec.eq_zero_or_eq_one (v8475 s i) with sequential | redirect
    · simp only [sequential, BitVec.reduceEq, ↓reduceIte] at fetch ⊢
      split
      · exact pipeline.ahead valid
      · rename_i cancelled
        have hold := cancelled_without_redirect_holds s i noReturn (started valid) sequential cancelled
        rw [fetch, hold]
        simpa using pipeline.ahead valid
    · rw [redirect_cancel s i redirect, fetch, redirect_saved_target s i reset env redirect]
      simp [redirect]
  · have nop := bubbles.fetch bubble
    have decode := nop_fetch_decode s i nop
    have taken := no_branch_mode_not_taken s i decode.2
    have check : v8475 s i = 0 := by
      simp [v8475, v8474, v42, decode.1, taken]
    have cancel : v7519 s i = 0 := by
      simp [fetch_cancel_pc_select, decode.1]
    have frontier := pipeline.frontier
    simp only [frontPc, bubble, BitVec.reduceEq, ↓reduceIte] at frontier
    rw [← reference] at frontier
    rw [bubble, cancel, taken, fetch]
    simp only [check, decode.1, BitVec.reduceEq, ↓reduceIte]
    rw [← frontier]
    rcases BitVec.eq_zero_or_eq_one s.g4.r136_ndut_5Fdpath_5Fstarted with h | h <;>
      simp [h]

#print axioms started_zero_of_valid_reachable
#print axioms pipeline_frontier_step
end RiscvMiniProofs
