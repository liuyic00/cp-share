import Proofs.MemoryPipeline
namespace NutShellProofs
open nNutCore
def MemoryUnit (instr : BitVec 64) (unit : BitVec 3) : Prop :=
  ∀ op, IsMemory op instr → unit = 1 ∨ unit = 3
theorem idu_memory_unit_0 (s : State) (i : Inputs) :
    MemoryUnit (v26210 s i) (v28254 s i) := by
  intro operation matched
  rcases BitVec.eq_zero_or_eq_one (v28077 s i) with zero | one
  · left
    have normal : v26384 s i = 0 := zero
    cases operation with
    | lb => exact (idu_memory_0_lb_decode s i normal matched).1
    | lh => exact (idu_memory_0_lh_decode s i normal matched).1
    | lw => exact (idu_memory_0_lw_decode s i normal matched).1
    | ld => exact (idu_memory_0_ld_decode s i normal matched).1
    | lbu => exact (idu_memory_0_lbu_decode s i normal matched).1
    | lhu => exact (idu_memory_0_lhu_decode s i normal matched).1
    | lwu => exact (idu_memory_0_lwu_decode s i normal matched).1
    | sb => exact (idu_memory_0_sb_decode s i normal matched).1
    | sh => exact (idu_memory_0_sh_decode s i normal matched).1
    | sw => exact (idu_memory_0_sw_decode s i normal matched).1
    | sd => exact (idu_memory_0_sd_decode s i normal matched).1
  · right; simp [v28254, one, v28078]
theorem idu_memory_unit_1 (s : State) (i : Inputs) :
    MemoryUnit (v26223 s i) (v28438 s i) := by
  intro operation matched
  rcases BitVec.eq_zero_or_eq_one (v28261 s i) with zero | one
  · left
    have normal : v26911 s i = 0 := zero
    cases operation with
    | lb => exact (idu_memory_1_lb_decode s i normal matched).1
    | lh => exact (idu_memory_1_lh_decode s i normal matched).1
    | lw => exact (idu_memory_1_lw_decode s i normal matched).1
    | ld => exact (idu_memory_1_ld_decode s i normal matched).1
    | lbu => exact (idu_memory_1_lbu_decode s i normal matched).1
    | lhu => exact (idu_memory_1_lhu_decode s i normal matched).1
    | lwu => exact (idu_memory_1_lwu_decode s i normal matched).1
    | sb => exact (idu_memory_1_sb_decode s i normal matched).1
    | sh => exact (idu_memory_1_sh_decode s i normal matched).1
    | sw => exact (idu_memory_1_sw_decode s i normal matched).1
    | sd => exact (idu_memory_1_sd_decode s i normal matched).1
  · right; simp [v28438, one, v28262]
end NutShellProofs
