import Proofs.BranchTarget
namespace NutShellProofs
open nNutCore

theorem branch_instruction_low2 (operation : BranchOp) (instr : BitVec 64)
    (matched : IsBranch operation instr) : BitVec.extractLsb' 0 2 instr = 3 := by
  have low := congrArg (BitVec.extractLsb' 0 2) matched
  cases operation <;>
    simp only [IsBranch, BranchOp.mask, BranchOp.encoding, BitVec.extractLsb'_and] at low
  all_goals
    change BitVec.extractLsb' 0 2 instr &&& BitVec.allOnes 2 = 3 at low
    simpa only [BitVec.and_allOnes] using low

theorem branch_sequential_pc (s : State) (i : Inputs) (operation : BranchOp)
    (matched : IsBranch operation s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v12202 s i = s.g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc + 4 := by
  have low := branch_instruction_low2 operation _ matched
  simp only [v12202, v12193, v12192, v12191, v11547, low, v2750]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, v12201, v12200,
    low_add _ _ (by decide : 39 ≤ 40), v12198,
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 39 ≤ 39),
    BitVec.extractLsb'_eq_self, v12145, v12144, v12199]
  rfl

theorem branch_next_pc_actual (s : State) (i : Inputs) (operation : BranchOp)
    (op : v28 s i = operation.control)
    (matched : IsBranch operation s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v12212 s i = if operation.condition (v12148 s i) (v12150 s i) then
      s.g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc +
        BitVec.extractLsb' 0 39 s.g48.r1566_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fdata_5Fimm
    else s.g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc + 4 := by
  have branch : v12182 s i = 1 := by
    cases operation <;> simp [v12182, v12181, v12141, op, BranchOp.control, v24]
  rw [v12212, v12190, v12189, branch_condition_actual s i operation op,
    branch, branch_target_actual s i operation op, branch_sequential_pc s i operation matched]
  split <;> simp_all [v24]

#print axioms branch_next_pc_actual
theorem branch_next_pc_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v12212 (run initial inputs (t + 1)) (inputs (t + 1)) =
      if operation.condition (v12148 (run initial inputs (t + 1)) (inputs (t + 1)))
        (v12150 (run initial inputs (t + 1)) (inputs (t + 1))) then
        (run initial inputs (t + 1)).g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc +
          BitVec.extractLsb' 0 39 (immediateB (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
      else (run initial inputs (t + 1)).g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc + 4 := by
  obtain ⟨op, _, _, imm, _⟩ := (branch_decode_run initial inputs reset t).2 valid operation matched unit
  have result := branch_next_pc_actual (run initial inputs (t + 1)) (inputs (t + 1)) operation op matched
  simpa only [imm] using result

#print axioms branch_next_pc_run
end NutShellProofs
