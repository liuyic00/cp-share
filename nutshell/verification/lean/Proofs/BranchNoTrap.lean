import Proofs.BranchLegalPipeline
import Proofs.AluExceptionSources
namespace NutShellProofs
open nNutCore

/-- Idle LSU cannot inject load/store misalignment into an ALU instruction. -/
theorem idle_lsu_alu_no_fault (s : State) (i : Inputs)
    (unit : v3 s i = 0) (idle : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0) :
    v11632 s i = 0 ∧ v11638 s i = 0 := by
  have inactive : v11546 s i = 0 := by
    simp [v11546, v11545, v11519, v2687, idle, v11530, v11525, v11524,
      v11522, v11521, v11520, unit]
  constructor
  · simp [v11632, v11631, v11630, v11586, v11573, inactive]
  · simp [v11638, v11637, v11636, v11634, inactive]

theorem branch_no_trap_with_idle_lsu_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : BranchOp)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (matched : IsBranch operation (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (idle : (run initial inputs (t + 1)).g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0) :
    v13725 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := by
  have illegal := (branch_legal_run initial inputs reset t).2 valid operation matched unit
  obtain ⟨loadFault, storeFault⟩ := idle_lsu_alu_no_fault _ _ unit idle
  exact alu_no_trap_remaining_sources_run initial inputs reset t valid unit illegal loadFault storeFault

#print axioms idle_lsu_alu_no_fault
#print axioms branch_no_trap_with_idle_lsu_run
end NutShellProofs
