import Proofs.AluInterruptSignal
namespace NutShellProofs
open nNutCore

/-- CSR-generated exceptions are disabled on ALU dispatch. -/
theorem alu_csr_exception_vector_zero (s : State) (i : Inputs) (unit : v3 s i = 0) :
    v13637 s i = 0 := by
  have csr : v13181 s i = 0 := by
    simp [v13181, v13180, v13178, v13177, v13176, unit]
  simp [v13485, v13486, v13487, v13488, v13489, v13490, v13491, v13492, v13493, v13494, v13495, v13496, v13497, v13498, v13499, v13500, v13501, v13502, v13503, v13504, v13505, v13506, v13507, v13508, v13509, v13510, v13511, v13512, v13513, v13514, v13515, v13516, v13517, v13518, v13519, v13520, v13521, v13522, v13523, v13524, v13525, v13630, v13631, v13632, v13633, v13634, v13635, v13636, v13637, v13454, v13451, v13185, v24, v4079, v8317, csr]

theorem alu_exception_vector_without_csr (s : State) (i : Inputs)
    (unit : v3 s i = 0) : v13683 s i = v13682 s i := by
  rw [v13683, alu_csr_exception_vector_zero s i unit]
  exact BitVec.zero_or

/-- Remaining trap sources are the carried exception bits and LSU fault insertions. -/
theorem alu_trap_sources_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    v13725 (run initial inputs (t + 1)) (inputs (t + 1)) =
      (if v13682 (run initial inputs (t + 1)) (inputs (t + 1)) ≠ 0 then 1 else 0) &&&
      v13724 (run initial inputs (t + 1)) (inputs (t + 1)) := by
  rw [alu_trap_is_exception_run initial inputs reset t valid unit]
  simp only [v13684, alu_exception_vector_without_csr _ _ unit, v9740]
  rfl

#print axioms alu_trap_sources_run
#print axioms alu_csr_exception_vector_zero
#print axioms alu_exception_vector_without_csr
end NutShellProofs
