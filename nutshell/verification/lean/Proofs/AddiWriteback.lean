import Proofs.AddiPipeline
import Proofs.ReferenceAddiSemantics
import Proofs.ImmediateArithmetic
namespace NutShellProofs
open nNutCore

/-- The ADDI mask excludes LUI, independently of high instruction bits. -/
theorem addi_not_lui (instr : BitVec 64) (addi : IsADDI instr) :
    BitVec.extractLsb' 0 7 instr ≠ 55 := by
  have opcode := opcode_of_mask instr (BitVec.ofNat 64 28799)
    (BitVec.ofNat 64 19) (by decide) addi.symm
  rw [opcode]
  decide

/-- ADDI writeback with instruction-derived immediate; no assumed source types,
operation selector, immediate field, or absence of exceptional decoding. -/
theorem writeback_addi_raw_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (addi : IsADDI (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      v12148 (run initial inputs (t + 1)) (inputs (t + 1)) +
      immediateI (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have decoded := (addi_decode_run initial inputs reset t).2 valid addi unit
  rcases decoded with ⟨op, kind1, kind2, imm, _write⟩
  have operand := execute_immediate_operand _ _ _
    (nonregister_operand_2_run initial inputs reset t) commit kind2
  have result := writeback_alu_add _ _ _ commit unit op
  simpa only [operand, imm] using result

/-- ADDI writeback after correspondence with the reference source register.
Architectural alignment remains an explicit induction premise. -/
theorem writeback_addi_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (addi : IsADDI (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      v15632 (run initial inputs (t + 2)) (inputs (t + 2)) +
      immediateI (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have decoded := (addi_decode_run initial inputs reset t).2 valid addi unit
  rcases decoded with ⟨op, kind1, kind2, imm, _write⟩
  have used := committed_reference_addi_uses_rs1 _ _ _ commit addi
  have result := writeback_register_immediate_add_run initial inputs reset t
    commit unit op kind1 kind2 aligned used (addi_not_lui _ addi)
  simpa only [imm] using result

#print axioms writeback_addi_raw_run
#print axioms writeback_addi_reference_run
/-- Equality with the actual ADDI result expression in the reference circuit.
This does not yet establish the destination/write-enable or whole-state induction. -/
theorem writeback_addi_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (addi : IsADDI (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      v16585 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  exact (writeback_addi_reference_run initial inputs reset t commit unit addi aligned).trans
    (committed_reference_addi_sum _ _ _ commit addi).symm

#print axioms writeback_addi_matches_reference_run
/-- Actual ADDI write enable, including the implemented LSU/CSR fault gates. -/
theorem writeback_addi_enabled_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (addi : IsADDI (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v11462 (run initial inputs (t + 2)) (inputs (t + 2)) = 1 := by
  have valid := commit_requires_execute_valid _ _ _ commit
  obtain ⟨_, _, _, _, enabled⟩ := (addi_decode_run initial inputs reset t).2 valid addi unit
  exact alu_next_writeback_enabled _ _ _ commit unit enabled

#print axioms writeback_addi_enabled_run
end NutShellProofs
