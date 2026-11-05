import Proofs.CommittedMemoryImmediate
namespace NutShellProofs
open nNutCore
theorem committed_reference_memory_uses_rs1 (s : State) (i next : Inputs)
    (operation : MemoryOp) (commit : v9 (step s i) next = 1)
    (matched : IsMemory operation (EXUPair s).1) :
    referenceUsesRs1 (step s i) next = true := by
  have low : v14575 (step s i) next &&& (28799 : BitVec 32) = operation.encoding.setWidth 32 := by
    rw [committed_reference_instruction s i next commit]
    exact store_match_low32 operation _ matched
  cases operation with
  | lb =>
    apply reference_uses_rs1_of_lb_match _ _ commit
    simp [v14893, v14890, v14892, v14891]
    exact low.symm
  | lh =>
    apply reference_uses_rs1_of_lh_match _ _ commit
    simp [v14885, v14882, v14884, v14883]
    exact low.symm
  | lw =>
    apply reference_uses_rs1_of_lw_match _ _ commit
    simp [v14877, v14874, v14876, v14875]
    exact low.symm
  | ld =>
    apply reference_uses_rs1_of_ld_match _ _ commit
    simp [v14710, v14707, v14709, v14708]
    exact low.symm
  | lbu =>
    apply reference_uses_rs1_of_lbu_match _ _ commit
    simp [v14869, v14866, v14868, v14867]
    exact low.symm
  | lhu =>
    apply reference_uses_rs1_of_lhu_match _ _ commit
    simp [v14861, v14858, v14860, v14859]
    exact low.symm
  | lwu =>
    apply reference_uses_rs1_of_lwu_match _ _ commit
    simp [v14718, v14715, v14717, v14716]
    exact low.symm
  | sb =>
    apply reference_uses_rs1_of_sb_match _ _ commit
    simp [v15186, v15183, v15185, v15184]
    exact low.symm
  | sh =>
    apply reference_uses_rs1_of_sh_match _ _ commit
    simp [v15180, v15177, v15179, v15178]
    exact low.symm
  | sw =>
    apply reference_uses_rs1_of_sw_match _ _ commit
    simp [v15174, v15171, v15173, v15172]
    exact low.symm
  | sd =>
    apply reference_uses_rs1_of_sd_match _ _ commit
    simp [v15160, v15157, v15159, v15158]
    exact low.symm
#print axioms committed_reference_memory_uses_rs1
end NutShellProofs
