import Proofs.MemoryAlignmentCorrespondence
import Proofs.ReferenceStoreValid
namespace NutShellProofs
open nNutCore
theorem reference_store_valid_alignment (s : State) (i : Inputs) (operation : MemoryOp)
    (store : operation.isLoad = false) (commit : v9 s i = 1)
    (matched : v14575 s i &&& 28799 = operation.encoding.setWidth 32) :
    v31224 s i = (if BitVec.extractLsb' 0 operation.alignmentBits
      (v15632 s i + v16164 s i) = 0 then 1 else 0) := by
  cases operation with
  | lb | lh | lw | ld | lbu | lhu | lwu => simp [MemoryOp.isLoad] at store
  | sb => exact reference_store_sb_valid s i commit matched
  | sh => exact reference_store_sh_valid s i commit matched
  | sw => exact reference_store_sw_valid s i commit matched
  | sd => exact reference_store_sd_valid s i commit matched
#print axioms reference_store_valid_alignment
theorem store_alignment_matches_reference_valid_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp) (store : operation.isLoad = false)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    v11628 (run initial inputs (t + 1)) (inputs (t + 1)) =
      v31224 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have op := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).1
  have low : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&& (28799 : BitVec 32) = operation.encoding.setWidth 32 := by
    have instruction := committed_reference_instruction _ _ _ commit
    change v14575 (run initial inputs (t + 2)) (inputs (t + 2)) =
      BitVec.extractLsb' 0 32 (EXUPair (run initial inputs (t + 1))).1 at instruction
    rw [instruction]
    exact store_match_low32 operation _ matched
  rw [normal_memory_alignment _ _ operation op
    (original_assumptions_lsu_idle_run initial inputs reset environment t),
    reference_store_valid_alignment _ _ operation store commit low,
    memory_address_reference_operands_run initial inputs reset environment t operation commit unit matched registers]
#print axioms store_alignment_matches_reference_valid_run
end NutShellProofs
