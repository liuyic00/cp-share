import Proofs.ReferenceLoadAddress
namespace NutShellProofs
open nNutCore

theorem load_address_matches_reference_node_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp)
    (load : operation.isLoad = true)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    v11612 (run initial inputs (t + 1)) (inputs (t + 1)) =
      v24059 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have low : v14575 (run initial inputs (t + 2)) (inputs (t + 2)) &&& (28799 : BitVec 32) = operation.encoding.setWidth 32 := by
    have instruction := committed_reference_instruction _ _ _ commit
    change v14575 (run initial inputs (t + 2)) (inputs (t + 2)) =
      BitVec.extractLsb' 0 32 (EXUPair (run initial inputs (t + 1))).1 at instruction
    rw [instruction]
    exact store_match_low32 operation _ matched
  have address := memory_address_reference_operands_run initial inputs reset environment t operation commit unit matched aligned
  cases operation with
  | sb | sh | sw | sd => simp [MemoryOp.isLoad] at load
  | lb => exact address.trans (reference_load_lb_address _ _ commit low).symm
  | lh => exact address.trans (reference_load_lh_address _ _ commit low).symm
  | lw => exact address.trans (reference_load_lw_address _ _ commit low).symm
  | ld => exact address.trans (reference_load_ld_address _ _ commit low).symm
  | lbu => exact address.trans (reference_load_lbu_address _ _ commit low).symm
  | lhu => exact address.trans (reference_load_lhu_address _ _ commit low).symm
  | lwu => exact address.trans (reference_load_lwu_address _ _ commit low).symm
#print axioms load_address_matches_reference_node_run
end NutShellProofs
