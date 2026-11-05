import Proofs.JumpPipeline
import Proofs.SignExtension
import Proofs.AluResults
namespace NutShellProofs
open nNutCore

theorem jump_control_branch_bit (operation : JumpOp) (instr : BitVec 64) :
    BitVec.extractLsb' 4 1 (jumpControl operation instr) = 1 := by
  cases operation <;> simp only [jumpControl]
  all_goals repeat' first | split | decide

theorem jump_instruction_full_width (operation : JumpOp) (instr : BitVec 64)
    (matched : IsJump operation instr) : BitVec.extractLsb' 0 2 instr = 3 := by
  change instr &&& operation.mask = operation.encoding at matched
  have low := congrArg (BitVec.extractLsb' 0 2) matched
  cases operation <;> simp only [BitVec.extractLsb'_and] at low
  all_goals change BitVec.extractLsb' 0 2 instr &&& BitVec.allOnes 2 = 3 at low
  all_goals simpa only [BitVec.and_allOnes] using low

theorem jump_link_result (s : State) (i : Inputs) (operation : JumpOp)
    (matched : IsJump operation s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (op : v28 s i = jumpControl operation s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v25095 s i = (v12145 s i).signExtend 64 + 4 := by
  have branch : v12142 s i = 1 := by
    change BitVec.extractLsb' 4 1 (v28 s i) = 1
    rw [op]
    exact jump_control_branch_bit _ _
  have full : v12192 s i = 3 := jump_instruction_full_width operation _ matched
  have extended : v25011 s i = (v12145 s i).signExtend 64 := by
    exact sign_extend_replication (v12145 s i) 25
  simp [v25095, v25094, v25093, branch, v25024, v25023, v25008,
    v12193, full, v2750, v24, v25015, v25014, v25012, v25013, extended,
    low_add _ _ (by decide : 64 ≤ 65),
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64)]

theorem jump_link_result_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : JumpOp)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump operation (EXUPair (run initial inputs (t + 1))).1) :
    v25095 (run initial inputs (t + 1)) (inputs (t + 1)) =
      (EXUPair (run initial inputs (t + 1))).2.signExtend 64 + 4 := by
  exact jump_link_result _ _ operation matched
    ((jump_decode_run initial inputs reset t).2 valid operation matched unit).1

#print axioms jump_link_result_run

theorem jump_link_writeback_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : JumpOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump operation (EXUPair (run initial inputs (t + 1))).1) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      (EXUPair (run initial inputs (t + 1))).2.signExtend 64 + 4 := by
  have captured := writeback_capture_0 _ _ _ commit unit
  exact captured.trans (jump_link_result_run initial inputs reset t operation
    (commit_requires_execute_valid _ _ _ commit) unit matched)

#print axioms jump_link_writeback_run
end NutShellProofs
