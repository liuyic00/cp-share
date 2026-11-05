import Proofs.MemoryUnitPipeline
namespace NutShellProofs
open nNutCore

/-- A valid instruction outside LSU and CSR cannot have a memory encoding. -/
theorem non_lsu_non_csr_instruction_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (notLSU : v3 (run initial inputs (t + 1)) (inputs (t + 1)) ≠ 1)
    (notCSR : v3 (run initial inputs (t + 1)) (inputs (t + 1)) ≠ 3) :
    ∀ operation, ¬ IsMemory operation (EXUPair (run initial inputs (t + 1))).1 := by
  intro operation matched
  have units := (memory_unit_decode_run initial inputs reset t).2 valid operation matched
  rcases units with lsu | csr
  · exact notLSU lsu
  · exact notCSR csr
#print axioms non_lsu_non_csr_instruction_run
end NutShellProofs
