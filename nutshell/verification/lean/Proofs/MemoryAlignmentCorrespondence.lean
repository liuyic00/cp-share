import Proofs.ReferenceLoadValid
import Proofs.MemoryAlignmentHold
namespace NutShellProofs
open nNutCore

def MemoryOp.alignmentBits : MemoryOp → Nat
  | .lb | .lbu | .sb => 0
  | .lh | .lhu | .sh => 1
  | .lw | .lwu | .sw => 2
  | .ld | .sd => 3

theorem normal_memory_alignment (s : State) (i : Inputs) (operation : MemoryOp)
    (op : v28 s i = operation.control)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0) :
    v11628 s i = (if BitVec.extractLsb' 0 operation.alignmentBits (v11612 s i) = 0 then 1 else 0) := by
  cases operation <;>
    simp [v11628, v11622, v11627, v11616, v11621, v11623, v11626,
      v11624, v11625, v11589, v11615, v11591, v11614, v11613,
      v11617, v11620, v11618, v11619, v11587, v11588, v11590,
      v24, v9721, v2750, v11569, v11568, v11519, v2687, outer,
      v11526, op, MemoryOp.control, MemoryOp.alignmentBits]

theorem reference_load_valid_alignment (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) (commit : v9 s i = 1)
    (matched : v14575 s i &&& 28799 = operation.encoding.setWidth 32) :
    v31135 s i = (if BitVec.extractLsb' 0 operation.alignmentBits
      (v15632 s i + v16164 s i) = 0 then 1 else 0) := by
  cases operation with
  | lb => exact reference_load_lb_valid s i commit matched
  | lh => exact reference_load_lh_valid s i commit matched
  | lw => exact reference_load_lw_valid s i commit matched
  | ld => exact reference_load_ld_valid s i commit matched
  | lbu => exact reference_load_lbu_valid s i commit matched
  | lhu => exact reference_load_lhu_valid s i commit matched
  | lwu => exact reference_load_lwu_valid s i commit matched
  | sb => simp [MemoryOp.isLoad] at load
  | sh => simp [MemoryOp.isLoad] at load
  | sw => simp [MemoryOp.isLoad] at load
  | sd => simp [MemoryOp.isLoad] at load
#print axioms normal_memory_alignment
#print axioms reference_load_valid_alignment
theorem load_alignment_matches_reference_valid_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp) (load : operation.isLoad = true)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    v11628 (run initial inputs (t + 1)) (inputs (t + 1)) =
      v31135 (run initial inputs (t + 2)) (inputs (t + 2)) := by
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
    reference_load_valid_alignment _ _ operation load commit low,
    memory_address_reference_operands_run initial inputs reset environment t operation commit unit matched registers]
#print axioms load_alignment_matches_reference_valid_run
end NutShellProofs
