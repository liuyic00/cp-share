import Proofs.LoadAlignmentFlags
import Proofs.LoadMisalignedRegisters
namespace NutShellProofs
open nNutCore

theorem aligned_ld_reference_result (s : State) (i : Inputs)
    (aligned : referenceLoadAligned .ld s i) : v16189 s i = v16181 s i := by
  have low := (reference_load_alignment_flags s i .ld rfl).mp aligned
  have offset : v16186 s i = 0 := by
    simpa [v16186, v16185, v16184, v16182, v16183,
      low_add _ _ (by decide : 64 ≤ 65),
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64),
      MemoryOp.alignmentBits] using low
  rw [reference_load_shift, offset]
  simp
#print axioms aligned_ld_reference_result

theorem aligned_load_registers_preserved_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (operation : MemoryOp) (load : operation.isLoad = true)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (aligned : v11628 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (currentReset : (inputs (t + 2)).g0.nreset = 0) :
    ArchitecturalRegistersAligned (run initial inputs (t + 3)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
  have outer := original_assumptions_lsu_idle_run initial inputs reset environment t
  have write := aligned_load_writeback_enabled_run initial inputs reset t operation load commit unit matched aligned
  have destination := committed_load_destination_agrees _ _ _ operation load
    (destination1_decode_run initial inputs reset t).2 commit write matched
  have low : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&& (28799 : BitVec 32) = operation.encoding.setWidth 32 := by
    have instruction := committed_reference_instruction _ _ _ commit
    change v14575 (run initial inputs (t + 2)) (inputs (t + 2)) =
      BitVec.extractLsb' 0 32 (EXUPair (run initial inputs (t + 1))).1 at instruction
    rw [instruction]
    exact store_match_low32 operation _ matched
  have address := memory_address_reference_operands_run initial inputs reset environment t operation commit unit matched registers
  have alignment := aligned
  rw [normal_memory_alignment _ _ operation op outer, address] at alignment
  have flags : referenceLoadAligned operation (run initial inputs (t + 2)) (inputs (t + 2)) := by
    apply (reference_load_alignment_flags _ _ operation load).mpr
    split at alignment
    · assumption
    · contradiction
  obtain ⟨noFault, noFault'⟩ := memory_raw_alignment_excludes_fault _ _ aligned
  have result : v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      referenceLoadResult operation (run initial inputs (t + 2)) (inputs (t + 2)) := by
    cases operation with
    | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
    | ld =>
      have raw := committed_ld_writeback_reference_data _ _ _ commit unit op outer noFault noFault'
      change v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
        v16181 (run initial inputs (t + 2)) (inputs (t + 2)) at raw
      exact raw.trans (aligned_ld_reference_result _ _ flags).symm
    | lb => exact committed_lb_writeback_matches_reference_run initial inputs reset environment t commit unit matched registers noFault noFault'
    | lh => exact committed_lh_writeback_matches_reference_run initial inputs reset environment t commit unit matched registers noFault noFault'
    | lw => exact committed_lw_writeback_matches_reference_run initial inputs reset environment t commit unit matched registers noFault noFault'
    | lbu => exact committed_lbu_writeback_matches_reference_run initial inputs reset environment t commit unit matched registers noFault noFault'
    | lhu => exact committed_lhu_writeback_matches_reference_run initial inputs reset environment t commit unit matched registers noFault noFault'
    | lwu => exact committed_lwu_writeback_matches_reference_run initial inputs reset environment t commit unit matched registers noFault noFault'
  exact load_registers_aligned_step _ _ operation load currentReset commit low flags registers destination write result
#print axioms aligned_load_registers_preserved_run
theorem load_registers_preserved_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (operation : MemoryOp) (load : operation.isLoad = true)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (currentReset : (inputs (t + 2)).g0.nreset = 0) :
    ArchitecturalRegistersAligned (run initial inputs (t + 3)) := by
  rcases BitVec.eq_zero_or_eq_one (v11628 (run initial inputs (t + 1)) (inputs (t + 1))) with misaligned | aligned
  · have valid := commit_requires_execute_valid _ _ _ commit
    have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
    have outer := original_assumptions_lsu_idle_run initial inputs reset environment t
    have low : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&& (28799 : BitVec 32) = operation.encoding.setWidth 32 := by
      have instruction := committed_reference_instruction _ _ _ commit
      change v14575 (run initial inputs (t + 2)) (inputs (t + 2)) =
        BitVec.extractLsb' 0 32 (EXUPair (run initial inputs (t + 1))).1 at instruction
      rw [instruction]
      exact store_match_low32 operation _ matched
    have disabled := misaligned_memory_writeback_disabled_run initial inputs reset environment t operation commit unit matched misaligned
    have flags : ¬ referenceLoadAligned operation (run initial inputs (t + 2)) (inputs (t + 2)) := by
      intro flag
      have bits := (reference_load_alignment_flags _ _ operation load).mp flag
      have address := memory_address_reference_operands_run initial inputs reset environment t operation commit unit matched registers
      rw [normal_memory_alignment _ _ operation op outer, address, if_pos bits] at misaligned
      contradiction
    exact misaligned_load_registers_aligned_step _ _ operation load currentReset commit low flags registers disabled
  · exact aligned_load_registers_preserved_run initial inputs reset environment t operation load commit unit matched registers aligned currentReset
#print axioms load_registers_preserved_run
end NutShellProofs
