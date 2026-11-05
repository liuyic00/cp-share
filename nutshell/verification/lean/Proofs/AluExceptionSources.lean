import Proofs.AluExceptions
import Proofs.AluPageFaults
import Proofs.AluAccessFaults
import Proofs.AluConstantExceptions
namespace NutShellProofs
open nNutCore

theorem alu_no_exception_remaining_sources_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (illegal : v13672 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (loadFault : v11632 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (storeFault : v11638 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    v13684 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := by
  have constants := (alu_constant_exception_run initial inputs reset t).2 valid unit
  rcases constants with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩
  have page := (alu_page_fault_run initial inputs reset t).2 valid unit
  have access := (alu_access_fault_run initial inputs reset t).2 valid unit
  simp only [v13672] at illegal
  simp [v13684, alu_exception_vector_without_csr _ _ unit, v13638, v13639, v13640, v13641, v13642, v13643, v13644, v13645, v13646, v13647, v13648, v13649, v13650, v13651, v13652, v13653, v13654, v13655, v13656, v13657, v13658, v13659, v13660, v13661, v13662, v13663, v13664, v13665, v13666, v13667, v13668, v13669, v13670, v13671, v13672, v13673, v13674, v13675, v13676, v13677, v13678, v13679, v13680, v13681, v13682, v9740, illegal, loadFault, storeFault, page, access, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

theorem alu_no_trap_remaining_sources_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (illegal : v13672 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (loadFault : v11632 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (storeFault : v11638 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    v13725 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := by
  have noException := alu_no_exception_remaining_sources_run initial inputs reset t valid unit
    illegal loadFault storeFault
  rw [alu_trap_is_exception_run initial inputs reset t valid unit, noException]
  exact BitVec.zero_and

#print axioms alu_no_trap_remaining_sources_run
#print axioms alu_no_exception_remaining_sources_run
end NutShellProofs
