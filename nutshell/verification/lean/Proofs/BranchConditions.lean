import Proofs.BranchPipeline
import Proofs.AluComparisons
namespace NutShellProofs
open nNutCore

def BranchOp.condition (operation : BranchOp) (x y : BitVec 64) : Prop :=
  match operation with
  | .beq => x = y | .bne => x ≠ y
  | .blt => x.toInt < y.toInt | .bge => ¬ x.toInt < y.toInt
  | .bltu => x.toNat < y.toNat | .bgeu => ¬ x.toNat < y.toNat

instance (operation : BranchOp) (x y : BitVec 64) : Decidable (operation.condition x y) := by
  cases operation <;> unfold BranchOp.condition <;> infer_instance

theorem branch_condition_actual (s : State) (i : Inputs) (operation : BranchOp)
    (op : v28 s i = operation.control) :
    v12179 s i = if operation.condition (v12148 s i) (v12150 s i) then 1 else 0 := by
  have subtract : BitVec.extractLsb' 6 1 (v28 s i) = 0 := by
    rw [op]; cases operation <;> decide
  have signed := alu_signed_compare_bit s i subtract
  have unsigned := alu_unsigned_compare_bit s i subtract
  cases operation <;>
    simp only [v12179, v12178, v12177, v12176, v12175, v12174, v12173,
      v12155, v12154, v12153, v12152, v12151, v12147, v12146, v12141,
      v4079, v4051, v9721, v2750, v24, op, BranchOp.control, BranchOp.condition,
      signed, unsigned] <;> simp <;> split <;> simp_all

#print axioms branch_condition_actual
theorem branch_condition_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v12179 (run initial inputs (t + 1)) (inputs (t + 1)) =
      if operation.condition (v12148 (run initial inputs (t + 1)) (inputs (t + 1)))
        (v12150 (run initial inputs (t + 1)) (inputs (t + 1))) then 1 else 0 := by
  exact branch_condition_actual _ _ operation
    ((branch_decode_run initial inputs reset t).2 valid operation matched unit).1

#print axioms branch_condition_run
end NutShellProofs
