import Proofs.BranchConditions
import Proofs.ArithmeticBits
namespace NutShellProofs
open nNutCore

theorem branch_target_actual (s : State) (i : Inputs) (operation : BranchOp)
    (op : v28 s i = operation.control) :
    v12211 s i = s.g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc +
      BitVec.extractLsb' 0 39 s.g48.r1566_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fimm := by
  have branch : v12182 s i = 1 := by
    cases operation <;> simp [v12182, v12181, v12141, op, BranchOp.control, v24]
  simp only [v12211, v12210, branch, ↓reduceIte, v12209,
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 39 ≤ 64),
    v12208, low_low _ (by decide : 39 ≤ 64), v12207,
    low_add _ _ (by decide : 39 ≤ 65), v12204, v12206,
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 39 ≤ 39),
    BitVec.extractLsb'_eq_self, v12145, v12144, v12205, v11595]

#print axioms branch_target_actual
theorem branch_target_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v12211 (run initial inputs (t + 1)) (inputs (t + 1)) =
      (run initial inputs (t + 1)).g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc +
      BitVec.extractLsb' 0 39 (immediateB (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) := by
  obtain ⟨op, _, _, imm, _⟩ := (branch_decode_run initial inputs reset t).2 valid operation matched unit
  have result := branch_target_actual (run initial inputs (t + 1)) (inputs (t + 1)) operation op
  simpa only [imm] using result

#print axioms branch_target_run
end NutShellProofs
