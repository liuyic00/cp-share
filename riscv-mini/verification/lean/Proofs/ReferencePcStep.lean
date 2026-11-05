import Proofs.PcBridge
import Proofs.ReferenceJump
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedSimpArgs false

theorem event_validity_iff_no_reference_event (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) :
    TaskHolds ⟨40, by decide⟩ s i ↔ v6727 s i = 0 := by
  have trap := environment_no_trap s i reset env
  change decide (v9586 s i ≠ 1 ∨ v9583 s i = 1) = true ↔ _
  rcases BitVec.eq_zero_or_eq_one (v964 s i) with idle | commit
  · have event : v6727 s i = 0 := by simp [v6727, idle, v4]
    simp [v9586, v9584, v9585, v9583, v9579, v9578, v9582, v9581,
      v9580, v955, v1, v0, v4, reset, trap, idle, event]
  · rcases BitVec.eq_zero_or_eq_one (v6727 s i) with event | event <;>
      simp [v9586, v9584, v9585, v9583, v9579, v9578, v9582, v9581,
        v9580, v955, v1, v0, v4, reset, trap, commit, event]


-- The normal PC mux still contains branch conditions and alignment guards.
-- No claim is made here that the reference event wire is always zero.
theorem reference_pc_no_event (s : State) (i : Inputs)
    (reset : i.nreset = 0) (commit : v964 s i = 1) (event : v6727 s i = 0) :
    (step s i).g2.r85_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fpc =
      if v6832 s i = 0 then v2222 s i + 4 else v6907 s i := by
  change v6936 s i = _
  simp only [v6936, v956, v955, v1, v0, reset, BitVec.reduceEq, ↓reduceIte,
    v6935, v6934, v6933, commit, v6931, event, v6930, v32,
    v6908, v6847, v6846, v6845, v4]
  have sequential : v6851 s i = v2222 s i + 4 := reference_jal_link s i
  rw [sequential]
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  simp [BitVec.getLsbD_extractLsb', BitVec.getLsbD_append (n := 2) (m := 32), hj]

#print axioms event_validity_iff_no_reference_event
#print axioms reference_pc_no_event
end RiscvMiniProofs
