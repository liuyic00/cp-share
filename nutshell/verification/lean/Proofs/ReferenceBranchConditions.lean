import Proofs.BranchReferenceCondition
import Proofs.ArithmeticBits
namespace NutShellProofs
open nNutCore

/-- Actual predicate nodes used by the reference PC update. -/
def referenceBranchCondition (operation : BranchOp) (s : State) (i : Inputs) : BitVec 1 :=
  match operation with
  | .beq => v23335 s i | .bne => v23311 s i
  | .blt => v23287 s i | .bge => v23239 s i
  | .bltu => v23263 s i | .bgeu => v23215 s i

theorem reference_branch_condition (operation : BranchOp) (s : State) (i : Inputs) :
    referenceBranchCondition operation s i =
      if operation.condition (v15632 s i) (v15394 s i) then 1 else 0 := by
  cases operation <;>
    simp [referenceBranchCondition, BranchOp.condition, v23335, v23311, v23287,
      v23239, v23263, v23215, Nat.not_lt, Int.not_lt]

theorem branch_condition_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    v12179 (run initial inputs (t + 1)) (inputs (t + 1)) =
      referenceBranchCondition operation (run initial inputs (t + 2)) (inputs (t + 2)) := by
  rw [reference_branch_condition]
  exact branch_condition_reference_run initial inputs reset t operation commit unit matched aligned

#print axioms branch_condition_matches_reference_run


def referenceBranchTarget (operation : BranchOp) (s : State) (i : Inputs) : BitVec 64 :=
  match operation with
  | .beq => v23588 s i | .bne => v23584 s i
  | .blt => v23580 s i | .bge => v23572 s i
  | .bltu => v23576 s i | .bgeu => v23568 s i

theorem reference_branch_target (operation : BranchOp) (s : State) (i : Inputs) :
    referenceBranchTarget operation s i = v16457 s i + v16164 s i := by
  cases operation <;>
    simp only [referenceBranchTarget, v23565, v23566, v23567, v23568, v23569, v23570, v23571, v23572, v23573, v23574, v23575, v23576, v23577, v23578, v23579, v23580, v23581, v23582, v23583, v23584, v23585, v23586, v23587, v23588,
      low_add _ _ (by decide : 64 ≤ 65),
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64),
      BitVec.extractLsb'_eq_self]

#print axioms reference_branch_target
end NutShellProofs
