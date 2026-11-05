import Proofs.ALURedirectAlignment
import Proofs.TemporaryTrapVectors
import Proofs.ExecuteFullWidth
import Proofs.TemporaryRegisterInvariant
namespace NutShellProofs
open nNutCore

theorem nontrapping_lsu_has_no_redirect (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 1)
    (noTrap : v13725 s i = 0) : v8 (step s i) next = 0 := by
  change v25388 s i = 0
  rw [v25388, if_pos (commit_requires_capture s i next commit)]
  simp [v25387, v25386, v25339, v27, v26, v7, v5, v4, unit,
    v25385, v25354, v25353, v25349, v25348, v25352, v13454, v13451,
    v13185, v13181, v13180, v13178, v13177, v13176, noTrap,
    v25384, v25383, v25382, v12140, v12139, v12137, v12136, v12135]

theorem temporary_pc32_redirect_aligned_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (executePC : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 →
      BitVec.extractLsb' 0 2
        (run initial inputs (t + 1)).g47.r1513_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Fpc = 0)
    (redirect : v14 (run initial inputs (t + 2)) (inputs (t + 2)) = 1) :
    BitVec.extractLsb' 0 2 (v2709 (run initial inputs (t + 2)) (inputs (t + 2))) = 0 := by
  have commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v9 (run initial inputs (t + 2)) (inputs (t + 2))) with zero | one
    · simp [v14, v13, v12, v11, v10, zero] at redirect
    · exact one
  have active : v8 (run initial inputs (t + 2)) (inputs (t + 2)) = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v8 (run initial inputs (t + 2)) (inputs (t + 2))) with zero | one
    · simp [v14, v13, v12, v11, v10, zero] at redirect
    · exact one
  have valid := commit_requires_execute_valid
    (run initial inputs (t + 1)) (inputs (t + 1)) (inputs (t + 2)) commit
  rcases BitVec.eq_zero_or_eq_one (v13725 (run initial inputs (t + 1)) (inputs (t + 1))) with noTrap | trap
  · rcases temporary_pc32_execute_alulsu initial inputs reset environment restriction t valid with alu | lsu
    · have noReset : (inputs (t + 1)).g0.nreset = 0 := by
        rcases BitVec.eq_zero_or_eq_one (inputs (t + 1)).g0.nreset with zero | one
        · exact zero
        · have idle := reset_has_no_next_commit (run initial inputs (t + 1))
            (inputs (t + 1)) (inputs (t + 2)) one
          change v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 at idle
          rw [idle] at commit
          contradiction
      exact committed_alu_redirect_aligned _ _ _ (environment (t + 1)) noReset
        commit alu noTrap active (execute_sequential_target_aligned _ _ (executePC valid)
          (original_execute_full_width_run initial inputs reset environment t valid))
    · have no := nontrapping_lsu_has_no_redirect _ _ _ commit lsu noTrap
      change v8 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 at no
      rw [no] at active
      contradiction
  · rw [temporary_pc32_committed_trap_target_zero_run initial inputs reset environment restriction t commit trap]
    rfl

#print axioms nontrapping_lsu_has_no_redirect
#print axioms temporary_pc32_redirect_aligned_run
end NutShellProofs
