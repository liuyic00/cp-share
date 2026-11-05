import Proofs.PcRelation
import Proofs.ExecuteTransfer
namespace RiscvMiniProofs
open nCoreSoc

-- Bubbles do not denote architectural instructions and need not have matching PCs.
def ValidWritebackPcAgreement (s : State) : Prop :=
  s.g4.r144_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG_5F1 = 0 → WritebackPcAgreement s

theorem pc_task_iff_agreement (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) :
    TaskHolds ⟨7, by decide⟩ s i ↔ WritebackPcAgreement s := by
  have committed : v962 s i = 1 := commit
  change decide (v9271 s i ≠ 1 ∨ v9269 s i = 1) = true ↔ _
  simp [v9271, v9270, v9269, v9268, v9267, v955, v1, v0, v4,
    reset, committed, WritebackPcAgreement]

theorem commit_iff_valid_writeback (s : State) (i : Inputs) (reset : i.nreset = 0) :
    v964 s i = 1 ↔ s.g4.r144_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG_5F1 = 0 := by
  simp [v964, v963, v962, v961, v960, v959, v1, v0, v4,
    no_stall_after_reset s i reset, reset]

theorem pc_task_iff_valid_agreement (s : State) (i : Inputs) (reset : i.nreset = 0) :
    TaskHolds ⟨7, by decide⟩ s i ↔ ValidWritebackPcAgreement s := by
  change decide (v9271 s i ≠ 1 ∨ v9269 s i = 1) = true ↔ _
  by_cases valid : s.g4.r144_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG_5F1 = 0#1 <;>
    simp [valid, v9271, v9270, v9269, v9268, v9267, v955, v1, v0, v4,
    v962, v961, v960, v959, no_stall_after_reset s i reset,
    reset, ValidWritebackPcAgreement, WritebackPcAgreement]

theorem valid_writeback_pc_reset (s : State) (i : Inputs) (reset : i.nreset = 1) :
    ValidWritebackPcAgreement (step s i) := by
  intro valid
  change v8567 s i = 0 at valid
  simp [v8567, v1, v0, reset, v512] at valid

-- The unguarded relation is actually false after reset; this is not an assertion failure.
theorem writeback_pc_disagrees_after_reset (s : State) (i : Inputs) (reset : i.nreset = 1) :
    ¬ WritebackPcAgreement (step s i) := by
  change v7783 s i ≠ v6936 s i
  simp [v7783, v6936, v956, v955, v1, v0, reset, v3, v6476]

theorem reference_pc_idle (s : State) (i : Inputs)
    (reset : i.nreset = 0) (idle : v964 s i ≠ 1) :
    (step s i).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      s.g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc := by
  have idle' : v964 s i ≠ 1#1 := idle
  change v6936 s i = _
  simp [v6936, v956, v955, v1, v0, reset, v6935, v6934, v6933,
    idle', v6932, v32, v2222]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [BitVec.getLsbD_append (n := 2) (m := 32), hj]

-- Exact remaining step obligation: a live FE instruction must carry the PC
-- that the reference will have after the current writeback instruction retires.
theorem valid_writeback_pc_step_iff (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) :
    ValidWritebackPcAgreement (step s i) ↔
      (s.g4.r143_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG = 0 →
        s.g3.r124_ndut_5Fdpath_5Ffe_5Freg_5Fpc =
          (step s i).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc) := by
  have transfer := (execute_transfer_step s i reset env).pc
  have trap := environment_no_trap s i reset env
  change (v8567 s i = 0 → _ = _) ↔ _
  rw [transfer]
  simp [v8567, v8566, v1, v0, reset, trap]

theorem valid_writeback_pc_after_reset_prefix (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) :
    ValidWritebackPcAgreement (run initial inputs cycles) := by
  cases cycles with
  | zero => have := reset.1; omega
  | succ n =>
    exact valid_writeback_pc_reset _ _ (reset.2.1 n (Nat.lt_succ_self n))

theorem pc_task_after_reset_prefix (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) :
    TaskHolds ⟨7, by decide⟩ (run initial inputs cycles) (inputs cycles) :=
  (pc_task_iff_valid_agreement _ _ (reset.2.2 cycles (Nat.le_refl _))).mpr
    (valid_writeback_pc_after_reset_prefix initial inputs cycles reset)

theorem valid_writeback_pc_idle_step_iff (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (idle : v964 s i ≠ 1) :
    ValidWritebackPcAgreement (step s i) ↔
      (s.g4.r143_ndut_5Fdpath_5FinstCommit_5Fpredit_5FREG = 0 →
        s.g3.r124_ndut_5Fdpath_5Ffe_5Freg_5Fpc =
          s.g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc) := by
  rw [valid_writeback_pc_step_iff s i reset env, reference_pc_idle s i reset idle]

#print axioms pc_task_after_reset_prefix
#print axioms valid_writeback_pc_idle_step_iff
#print axioms pc_task_iff_valid_agreement
#print axioms valid_writeback_pc_step_iff
#print axioms reference_pc_idle
#print axioms writeback_pc_disagrees_after_reset
end RiscvMiniProofs
