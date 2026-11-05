import Proofs.MemoryPipeline
import Proofs.LSUIdleInvariant
import Proofs.ImmediateArithmetic
namespace NutShellProofs
open nNutCore

theorem lsu_address_sum (s : State) (i : Inputs)
    (idle : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0) :
    v11612 s i = v11592 s i + v11595 s i := by
  simp [v11612, v11611, v11519, idle, v2687, v11599, v11598,
    v11594, v11597, v11593, v11596,
    low_add _ _ (by decide : 64 ≤ 65),
    BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64)]

theorem memory_address_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation
      (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr) :
    v11612 (run initial inputs (t + 1)) (inputs (t + 1)) =
      v11592 (run initial inputs (t + 1)) (inputs (t + 1)) +
        memoryImmediate operation
          (run initial inputs (t + 1)).g47.r1512_nbackend_5Fexu_5Fio_5Fin_5Fbits_5Fr_5Fcf_5Finstr := by
  have immediate := ((memory_decode_run initial inputs reset t).2 valid operation matched unit).2.2.2.1
  rw [lsu_address_sum _ _ (original_assumptions_lsu_idle_run initial inputs reset environment t)]
  exact congrArg (fun imm : BitVec 64 => v11592 (run initial inputs (t + 1)) (inputs (t + 1)) + imm) immediate
#print axioms lsu_address_sum
#print axioms memory_address_run
end NutShellProofs
