import Proofs.StoreCheckerData
import Proofs.StoreOperandCorrespondence
import Proofs.StoreAddressRun
namespace NutShellProofs
open nNutCore
theorem store_data_task8_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp) (store : operation.isLoad = false)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    TaskHolds 8 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
  rcases BitVec.eq_zero_or_eq_one (v11628 (run initial inputs (t + 1)) (inputs (t + 1))) with misaligned | aligned
  · have enabled := committed_normal_memory_enabled _ _ _ operation op
      (original_assumptions_lsu_idle_run initial inputs reset environment t) unit commit
    have dut := committed_fault_disables_store_valid _ _ _ commit
      (enabled_misalignment_fault _ _ enabled misaligned)
    change v31215 (run initial inputs (t + 2)) (inputs (t + 2)) = 0 at dut
    have refValid := store_alignment_matches_reference_valid_run initial inputs reset environment t
      operation store commit unit matched registers
    have refZero := refValid.symm.trans misaligned
    change decide (v31304 (run initial inputs (t + 2)) (inputs (t + 2)) ≠ 1 ∨
      v31302 (run initial inputs (t + 2)) (inputs (t + 2)) = 1) = true
    simp [v31304, v31233, dut, refZero]
  · have outer := original_assumptions_lsu_idle_run initial inputs reset environment t
    have size := completed_store_size_run initial inputs reset environment t operation store commit unit matched aligned
    have data := completed_checker_store_data_run initial inputs reset environment t commit unit aligned
    have operand := store_operand_matches_reference_run initial inputs reset t operation store commit unit matched registers
    have address := memory_address_reference_operands_run initial inputs reset environment t operation commit unit matched registers
    have refAligned : BitVec.extractLsb' 0 operation.alignmentBits
        (v15632 (run initial inputs (t + 2)) (inputs (t + 2)) +
          v16164 (run initial inputs (t + 2)) (inputs (t + 2))) = 0 := by
      have h := normal_memory_alignment _ (inputs (t + 1)) operation op outer
      rw [address, aligned] at h
      split at h
      · assumption
      · contradiction
    have low : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&& (28799 : BitVec 32) = operation.encoding.setWidth 32 := by
      have instruction := committed_reference_instruction _ _ _ commit
      change v14575 (run initial inputs (t + 2)) (inputs (t + 2)) =
        BitVec.extractLsb' 0 32 (EXUPair (run initial inputs (t + 1))).1 at instruction
      rw [instruction]
      exact store_match_low32 operation _ matched
    have equal : v31285 (run initial inputs (t + 2)) (inputs (t + 2)) =
        v31301 (run initial inputs (t + 2)) (inputs (t + 2)) := by
      cases operation with
      | lb | lh | lw | ld | lbu | lhu | lwu => simp [MemoryOp.isLoad] at store
      | sb =>
        have formatted := store_sb_formatted_low _ (inputs (t + 1)) op outer
        have actual := store_checker_data_size_8 _ _ size
        have reference := reference_store_sb_data _ _ commit low
        rw [data, formatted, operand] at actual
        simp only [MemoryOp.alignmentBits] at refAligned
        rw [if_pos refAligned] at reference
        exact actual.trans reference.symm
      | sh =>
        have formatted := store_sh_formatted_low _ (inputs (t + 1)) op outer
        have actual := store_checker_data_size_16 _ _ size
        have reference := reference_store_sh_data _ _ commit low
        rw [data, formatted, operand] at actual
        simp only [MemoryOp.alignmentBits] at refAligned
        rw [if_pos refAligned] at reference
        exact actual.trans reference.symm
      | sw =>
        have formatted := store_sw_formatted_low _ (inputs (t + 1)) op outer
        have actual := store_checker_data_size_32 _ _ size
        have reference := reference_store_sw_data _ _ commit low
        rw [data, formatted, operand] at actual
        simp only [MemoryOp.alignmentBits] at refAligned
        rw [if_pos refAligned] at reference
        exact actual.trans reference.symm
      | sd =>
        have formatted := store_sd_formatted_low _ (inputs (t + 1)) op outer
        have actual := store_checker_data_size_64 _ _ size
        have reference := reference_store_sd_data _ _ commit low
        rw [data, formatted, operand] at actual
        simp only [MemoryOp.alignmentBits] at refAligned
        rw [if_pos refAligned] at reference
        exact actual.trans reference.symm
    change decide (v31304 (run initial inputs (t + 2)) (inputs (t + 2)) ≠ 1 ∨
      v31302 (run initial inputs (t + 2)) (inputs (t + 2)) = 1) = true
    simp [v31302, equal]
#print axioms store_data_task8_run
end NutShellProofs
