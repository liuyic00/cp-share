import Proofs.JumpNoTrap
import Proofs.ReferenceJumpPC
import Proofs.FrontendRedirectPC
namespace NutShellProofs
open nNutCore
theorem committed_jump_redirect_valid (s : State) (i next : Inputs)
    (operation : JumpOp) (instr : BitVec 64)
    (op : v28 s i = jumpControl operation instr)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0)
    (noTrap : v13725 s i = 0) :
    v8 (step s i) next = v12218 s i := by
  obtain ⟨mou, csr⟩ := alu_redirect_priority s i unit
  have noCSR := csr.trans noTrap
  have valid := commit_requires_execute_valid s i next commit
  have flush := commit_requires_unflushed s i next commit
  have branchBit : v12142 s i = 1 := by
    change BitVec.extractLsb' 4 1 (v28 s i) = 1
    rw [op]
    exact jump_control_branch_bit operation instr
  change v25388 s i = _
  rcases BitVec.eq_zero_or_eq_one (v12218 s i) with h | h <;>
    simp [h, v25388, commit_requires_capture s i next commit, v25387, v25386,
    mou, v25385, noCSR, v25384, v25383, v25382, branchBit,
    v12140, v12139, v12138, v12137, v12136, v12135, unit, valid, flush, v24]


theorem jal_recovery_from_original_assumptions_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump .jal (EXUPair (run initial inputs (t + 1))).1)
    (pc : TaskHolds 10 (run initial inputs (t + 2)) (inputs (t + 2)))
    (correction : v12218 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    (run initial inputs (t + 3)).g33.r1065_nfrontend_5Fifu_5Fpc =
      BitVec.extractLsb' 0 39
        (run initial inputs (t + 3)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have noTrap := jump_no_trap_run initial inputs reset environment t .jal valid unit matched
  have op := ((jump_decode_run initial inputs reset t).2 valid .jal matched unit).1
  have redirect := committed_jump_redirect_valid _ _ _ .jal _ op commit unit noTrap
  exact (frontend_pc_redirect _ _ currentReset commit (redirect.trans correction)).trans
    ((committed_alu_redirect_target _ _ _ commit unit noTrap).trans
      (jal_target_matches_updated_reference_pc_run initial inputs reset t
        (environment (t + 1)) currentReset commit unit matched pc))
#print axioms jal_recovery_from_original_assumptions_run

theorem jalr_recovery_from_original_assumptions_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (currentReset : (inputs (t + 2)).g0.nreset = 0)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsJump .jalr (EXUPair (run initial inputs (t + 1))).1)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (correction : v12218 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    (run initial inputs (t + 3)).g33.r1065_nfrontend_5Fifu_5Fpc =
      BitVec.extractLsb' 0 39
        (run initial inputs (t + 3)).g45.r1471_nbackend_5Fwbu_5Fchecker_5FspecCore_5Fstate_5Fpc := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have noTrap := jump_no_trap_run initial inputs reset environment t .jalr valid unit matched
  have op := ((jump_decode_run initial inputs reset t).2 valid .jalr matched unit).1
  have redirect := committed_jump_redirect_valid _ _ _ .jalr _ op commit unit noTrap
  exact (frontend_pc_redirect _ _ currentReset commit (redirect.trans correction)).trans
    ((committed_alu_redirect_target _ _ _ commit unit noTrap).trans
      (jalr_target_matches_updated_reference_pc_run initial inputs reset t
        (environment (t + 1)) currentReset commit unit matched aligned))
#print axioms jalr_recovery_from_original_assumptions_run
#print axioms committed_jump_redirect_valid
theorem accepted_jump_prediction_target (s : State) (i : Inputs)
    (operation : JumpOp) (instr : BitVec 64)
    (op : v28 s i = jumpControl operation instr)
    (accepted : v12218 s i = 0) : v12212 s i = v12215 s i := by
  have bits := jump_control_target_bits operation instr
  have jump : v12182 s i = 0 := by
    simp [v12182, v12181, v12141, op, bits.1, v24]
  by_cases mismatch : v12212 s i = v12215 s i
  · exact mismatch
  · simp [v12218, v12183, jump, v12217, v12216, v12213, mismatch] at accepted
#print axioms accepted_jump_prediction_target
end NutShellProofs
