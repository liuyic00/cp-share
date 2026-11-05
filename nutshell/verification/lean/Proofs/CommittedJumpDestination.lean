import Proofs.CommittedDestination
import Proofs.ReferenceJumpDestination
import Proofs.JumpLinkCorrespondence
namespace NutShellProofs
open nNutCore

private theorem destination_low32 (instr : BitVec 64) :
    BitVec.extractLsb' 7 5 (BitVec.extractLsb' 0 32 instr) =
      BitVec.extractLsb' 7 5 instr := by
  apply BitVec.eq_of_getLsbD_eq
  intro k
  simp only [BitVec.getLsbD_extractLsb']
  by_cases small : k < 5
  · have bound : 7 + k < 32 := by omega
    simp [small, bound]
  · simp [small]

theorem committed_jump_destination_agrees (s : State) (i next : Inputs)
    (operation : JumpOp) (decoded : ExecuteDestination1Decoded s)
    (commit : v9 (step s i) next = 1)
    (write : v11462 (step s i) next = 1)
    (addi : IsJump operation s.g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v11465 (step s i) next = v15142 (step s i) next := by
  have matched : v14575 (step s i) next &&& operation.mask.setWidth 32 = operation.encoding.setWidth 32 := by
    rw [committed_reference_instruction s i next commit]
    exact jump_match_low32 operation _ addi
  rw [reference_jump_destination _ _ operation commit matched,
    committed_reference_instruction s i next commit, destination_low32]
  exact committed_dut_destination s i next decoded write

#print axioms committed_jump_destination_agrees
theorem writeback_jump_enabled_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : JumpOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump operation (EXUPair (run initial inputs (t + 1))).1) :
    v11462 (run initial inputs (t + 2)) (inputs (t + 2)) = 1 := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨_, _, _, _, enabled⟩ :=
    (jump_decode_run initial inputs reset t).2 valid operation matched unit
  exact alu_next_writeback_enabled _ _ _ commit unit enabled
#print axioms writeback_jump_enabled_run
end NutShellProofs
