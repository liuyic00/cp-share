import Proofs.ReferencePCHold
namespace NutShellProofs
open nNutCore

/-- Without a commit or an accepted fetch, the actual frontend PC holds. -/
theorem frontend_pc_hold_without_commit_or_fetch (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (noCommit : v9 s i = 0) (noFetch : v9672 s i = 0) :
    (step s i).g33.r1065_nfrontend_5Fifu_5Fpc = s.g33.r1065_nfrontend_5Fifu_5Fpc := by
  have redirect : v14 s i = 0 := by
    simp [v14, v13, v12, v11, v10, noCommit]
  change v9675 s i = _
  simp [v9675, v1, v0, reset, v9674, v9673, redirect, noFetch]

theorem frontend_pc_hold_interval (initial : State) (inputs : Nat → Inputs)
    (start count : Nat)
    (quiet : ∀ k, k < count →
      (inputs (start + k)).g0.nreset = 0 ∧
      v9 (run initial inputs (start + k)) (inputs (start + k)) = 0 ∧
      v9672 (run initial inputs (start + k)) (inputs (start + k)) = 0) :
    (run initial inputs (start + count)).g33.r1065_nfrontend_5Fifu_5Fpc =
      (run initial inputs start).g33.r1065_nfrontend_5Fifu_5Fpc := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have now := quiet count (by omega)
    have prior := ih (fun k hk => quiet k (by omega))
    exact (frontend_pc_hold_without_commit_or_fetch _ _ now.1 now.2.1 now.2.2).trans prior

/-- Alignment established by recovery survives a joint fetch/commit stall. -/
theorem frontend_reference_pc_alignment_hold_interval (initial : State) (inputs : Nat → Inputs)
    (start count : Nat)
    (aligned : (run initial inputs start).g33.r1065_nfrontend_5Fifu_5Fpc =
      BitVec.extractLsb' 0 39
        (run initial inputs start).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc)
    (quiet : ∀ k, k < count →
      (inputs (start + k)).g0.nreset = 0 ∧
      v9 (run initial inputs (start + k)) (inputs (start + k)) = 0 ∧
      v9672 (run initial inputs (start + k)) (inputs (start + k)) = 0) :
    (run initial inputs (start + count)).g33.r1065_nfrontend_5Fifu_5Fpc =
      BitVec.extractLsb' 0 39
        (run initial inputs (start + count)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc := by
  have reference := reference_pc_hold_interval initial inputs start count
    (fun k hk => ⟨(quiet k hk).1, (quiet k hk).2.1⟩)
  exact (frontend_pc_hold_interval initial inputs start count quiet).trans
    (aligned.trans (congrArg (BitVec.extractLsb' 0 39) reference).symm)

#print axioms frontend_pc_hold_interval
#print axioms frontend_reference_pc_alignment_hold_interval
end NutShellProofs
