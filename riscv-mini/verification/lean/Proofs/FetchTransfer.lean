import Proofs.PcLowBit
import Proofs.PcSuccessor
namespace RiscvMiniProofs
open nCoreSoc

structure FetchTransfer (s next : State) (i : Inputs) : Prop where
  started : next.g4.r136_ndut_5Fdpath_5Fstarted = 0
  execute_pc : next.g3.r124_ndut_5Fdpath_5Ffe_5Freg_5Fpc =
    BitVec.extractLsb' 0 32 s.g4.r137_ndut_5Fdpath_5Fpc
  execute_cancel : next.g4.r143_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG =
    (s.g4.r136_ndut_5Fdpath_5Fstarted ||| v7519 s i) ||| v7759 s i
  writeback_cancel : next.g4.r144_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG_5F1 =
    s.g4.r143_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG
  check : next.g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = v8475 s i
  fetch_pc : next.g4.r137_ndut_5Fdpath_5Fpc =
    if v8475 s i = 1 then v8497 s i
    else if v8473 s i = 2 then s.g4.r137_ndut_5Fdpath_5Fpc else v8502 s i

theorem fetch_transfer_step (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i)
    (noReturn : s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst ≠ 268435571) :
    FetchTransfer s (step s i) i := by
  have trap := environment_no_trap s i reset env
  have stall := no_stall_after_reset s i reset
  have noSelect := no_legacy_return_select s i noReturn
  constructor
  · exact reset
  · change v7771 s i = _
    simp [v7771, v7770, v7769, v7297, v1, v0, v4, reset, stall]
  · change v8565 s i = _
    simp [v8565, v8564, v8563, v8562, v1, v0, reset, trap]
  · change v8567 s i = _
    simp [v8567, v8566, v1, v0, reset, trap]
  · change v8477 s i = _
    simp [v8477, v8476, v7774, v7773, v7772, v7777, v7776, v7775,
      v1, v0, v4, reset, trap, stall]
  · change v8508 s i = _
    simp [v8508, v8507, v8506, v8505, v8504, v8503, v8491, v8490,
      v8475, v8474, v8498, v42, v38, v1, v0, reset, trap, stall, noSelect]

theorem fetch_transfer_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) :
    FetchTransfer (run initial inputs t) (run initial inputs (t+1)) (inputs t) :=
  fetch_transfer_step _ _ (reset.2.2 t ht) (env t)
    (fetch_excludes_legacy_return initial inputs cycles reset env t ht)

#print axioms fetch_transfer_reachable
end RiscvMiniProofs
