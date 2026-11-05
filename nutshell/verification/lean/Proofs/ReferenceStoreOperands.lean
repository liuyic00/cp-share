import Proofs.ReferenceMemoryOperands
namespace NutShellProofs
open nNutCore
set_option maxRecDepth 4096
theorem committed_reference_store_uses_rs2 (s : State) (i next : Inputs)
    (operation : MemoryOp) (store : operation.isLoad = false) (commit : v9 (step s i) next = 1)
    (matched : IsMemory operation (EXUPair s).1) :
    referenceUsesRs2 (step s i) next = true := by
  have low : v14575 (step s i) next &&& (28799 : BitVec 32) = operation.encoding.setWidth 32 := by
    rw [committed_reference_instruction s i next commit]
    exact store_match_low32 operation _ matched

  cases operation with
  | lb | lh | lw | ld | lbu | lhu | lwu => simp [MemoryOp.isLoad] at store
  | sb =>
    apply reference_uses_rs2_of_store_sb_match _ _ commit
    simp [v15186, v15183, v15185, v15184]
    exact low.symm
  | sh =>
    apply reference_uses_rs2_of_store_sh_match _ _ commit
    simp [v15180, v15177, v15179, v15178]
    exact low.symm
  | sw =>
    apply reference_uses_rs2_of_store_sw_match _ _ commit
    simp [v15174, v15171, v15173, v15172]
    exact low.symm
  | sd =>
    apply reference_uses_rs2_of_store_sd_match _ _ commit
    simp [v15160, v15157, v15159, v15158]
    exact low.symm
#print axioms committed_reference_store_uses_rs2
end NutShellProofs
