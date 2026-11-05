import Proofs.ReferenceJumpImmediate
import Proofs.ReferenceAddi
namespace NutShellProofs
open nNutCore

theorem jump_match_low32 (operation : JumpOp) (instr : BitVec 64)
    (matched : IsJump operation instr) :
    BitVec.extractLsb' 0 32 instr &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32 := by
  have low := congrArg (BitVec.extractLsb' 0 32) matched
  cases operation <;> simpa only [BitVec.extractLsb'_and] using low

private theorem jump_extract_low32 (instr : BitVec 64) (start len : Nat)
    (bound : start + len ≤ 32) :
    BitVec.extractLsb' start len (BitVec.extractLsb' 0 32 instr) = BitVec.extractLsb' start len instr := by
  apply BitVec.eq_of_getLsbD_eq
  intro bit
  simp only [BitVec.getLsbD_extractLsb']
  by_cases small : bit < len
  · have inRange : start + bit < 32 := by omega
    simp [small, inRange]
  · simp [small]

theorem committed_reference_jump_immediate (s : State) (i next : Inputs)
    (operation : JumpOp) (commit : v9 (step s i) next = 1)
    (matched : IsJump operation (EXUPair s).1) :
    v16164 (step s i) next = jumpImmediate operation (EXUPair s).1 := by
  have low : v14575 (step s i) next &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32 := by
    rw [committed_reference_instruction s i next commit]
    exact jump_match_low32 operation _ matched
  cases operation with
  | jal =>
    have result := reference_jump_imm_jal_immediate (step s i) next commit low
    rw [committed_reference_instruction s i next commit] at result
    simpa only [jump_extract_low32 _ _ _ (by decide : 31 + 1 ≤ 32),
      jump_extract_low32 _ _ _ (by decide : 12 + 8 ≤ 32),
      jump_extract_low32 _ _ _ (by decide : 20 + 1 ≤ 32),
      jump_extract_low32 _ _ _ (by decide : 21 + 10 ≤ 32)] using result
  | jalr =>
    have result := reference_jump_imm_jalr_immediate (step s i) next commit low
    rw [committed_reference_instruction s i next commit] at result
    simpa only [jump_extract_low32 _ _ _ (by decide : 20 + 12 ≤ 32)] using result

theorem jump_immediate_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : JumpOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump operation (EXUPair (run initial inputs (t + 1))).1) :
    v12150 (run initial inputs (t + 1)) (inputs (t + 1)) =
      v16164 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  exact (jump_immediate_operand_run initial inputs reset t operation
    (commit_requires_execute_valid _ _ _ commit) unit matched).trans
    (committed_reference_jump_immediate _ _ _ operation commit matched).symm

#print axioms committed_reference_jump_immediate
#print axioms jump_immediate_matches_reference_run
end NutShellProofs
