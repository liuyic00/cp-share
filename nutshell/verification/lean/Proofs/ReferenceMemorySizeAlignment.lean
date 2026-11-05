import Proofs.MemorySizeRun
import Proofs.StoreAddressRun
namespace NutShellProofs
open nNutCore
theorem reference_load_size_alignment (s : State) (i : Inputs) (operation : MemoryOp)
    (direction : operation.isLoad = true) (commit : v9 s i = 1)
    (matched : v14575 s i &&& 28799 = operation.encoding.setWidth 32) :
    v31204 s i = (if BitVec.extractLsb' 0 operation.alignmentBits (v15632 s i + v16164 s i) = 0 then operation.sizeBits else 0) := by
  cases operation with
  | lb => exact reference_load_lb_size s i commit matched
  | lh => exact reference_load_lh_size s i commit matched
  | lw => exact reference_load_lw_size s i commit matched
  | ld => exact reference_load_ld_size s i commit matched
  | lbu => exact reference_load_lbu_size s i commit matched
  | lhu => exact reference_load_lhu_size s i commit matched
  | lwu => exact reference_load_lwu_size s i commit matched
  | sb => simp [MemoryOp.isLoad] at direction
  | sh => simp [MemoryOp.isLoad] at direction
  | sw => simp [MemoryOp.isLoad] at direction
  | sd => simp [MemoryOp.isLoad] at direction
#print axioms reference_load_size_alignment
theorem reference_store_size_alignment (s : State) (i : Inputs) (operation : MemoryOp)
    (direction : operation.isLoad = false) (commit : v9 s i = 1)
    (matched : v14575 s i &&& 28799 = operation.encoding.setWidth 32) :
    v31350 s i = (if BitVec.extractLsb' 0 operation.alignmentBits (v15632 s i + v16164 s i) = 0 then operation.sizeBits else 0) := by
  cases operation with
  | lb => simp [MemoryOp.isLoad] at direction
  | lh => simp [MemoryOp.isLoad] at direction
  | lw => simp [MemoryOp.isLoad] at direction
  | ld => simp [MemoryOp.isLoad] at direction
  | lbu => simp [MemoryOp.isLoad] at direction
  | lhu => simp [MemoryOp.isLoad] at direction
  | lwu => simp [MemoryOp.isLoad] at direction
  | sb => exact reference_store_sb_size s i commit matched
  | sh => exact reference_store_sh_size s i commit matched
  | sw => exact reference_store_sw_size s i commit matched
  | sd => exact reference_store_sd_size s i commit matched
#print axioms reference_store_size_alignment
end NutShellProofs
