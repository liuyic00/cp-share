import Proofs.RegisterALUPC
namespace NutShellProofs
open nNutCore

theorem reference_pc_hold (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (noCommit : v9 s i = 0) :
    (step s i).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc =
      s.g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc := by
  change v23683 s i = _
  simp [v23683, v14555, v14554, v14553, v11455, reset, v23682, v23681,
    v23680, v14560, v14559, v14558, noCommit, ↓reduceIte, v23679,
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64),
    BitVec.extractLsb'_eq_self, v16457]

/-- Actual reference PC is stable throughout any finite gap without commits or reset. -/
theorem reference_pc_hold_interval (initial : State) (inputs : Nat → Inputs)
    (start count : Nat)
    (quiet : ∀ k, k < count →
      (inputs (start + k)).g0.nreset = 0 ∧
      v9 (run initial inputs (start + k)) (inputs (start + k)) = 0) :
    (run initial inputs (start + count)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc =
      (run initial inputs start).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have now := quiet count (by omega)
    have prior := ih (fun k hk => quiet k (by omega))
    exact (reference_pc_hold _ _ now.1 now.2).trans prior

/-- Sequential reference advance remains visible after an arbitrary commit-free gap. -/
theorem register_alu_pc_after_gap (initial : State) (inputs : Nat → Inputs)
    (t count : Nat) (operation : RegisterALUOp)
    (reset : (inputs (t + 2)).g0.nreset = 0)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (matched : IsRegisterALU operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (quiet : ∀ k, k < count →
      (inputs (t + 3 + k)).g0.nreset = 0 ∧
      v9 (run initial inputs (t + 3 + k)) (inputs (t + 3 + k)) = 0) :
    (run initial inputs (t + 3 + count)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc =
      v16457 (run initial inputs (t + 2)) (inputs (t + 2)) + 4 := by
  exact (reference_pc_hold_interval initial inputs (t + 3) count quiet).trans
    (reference_register_alu_pc_run initial inputs t operation reset commit matched)

#print axioms reference_pc_hold_interval
#print axioms register_alu_pc_after_gap
end NutShellProofs
