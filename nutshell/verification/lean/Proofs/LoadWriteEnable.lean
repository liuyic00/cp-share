import Proofs.CommittedLoadDestination
import Proofs.MemoryPipeline
namespace NutShellProofs
open nNutCore

theorem aligned_lsu_next_writeback_enabled (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 1)
    (write : v11475 s i = 1) (aligned : v11628 s i = 1) :
    v11462 (step s i) next = 1 := by
  have notCSR : v13180 s i = 0 := by
    simp [v13180, v13178, v13177, v13176, unit]
  have loadFault : v11632 s i = 0 := by
    simp [v11632, v11631, v11630, v11629, aligned, v24]
  have storeFault : v11638 s i = 0 := by
    simp [v11638, v11637, v11636, v11635, aligned, v24]
  have wen : v11473 s i = 1 := write
  have emitted : v25485 s i = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v25478 s i) with other | other <;>
      simp [v25485, v25484, v25480, wen, v25479, v25477, v25475,
      v25473, v25472, v25471, v25474, v25476, loadFault, storeFault,
      v25483, v25482, notCSR, v24, other]
  have nextWen : v11459 (step s i) next = 1 :=
    (capture_decode_ctrl_rfWen s i next commit).trans emitted
  simp [v11462, v11461, v11460, nextWen, commit]

theorem aligned_load_writeback_enabled_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat) (operation : MemoryOp)
    (load : operation.isLoad = true)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (aligned : v11628 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    v11462 (run initial inputs (t + 2)) (inputs (t + 2)) = 1 := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have decoded := (memory_decode_run initial inputs reset t).2 valid operation matched unit
  have write : v11475 (run initial inputs (t + 1)) (inputs (t + 1)) = 1 := by
    simpa only [load, ↓reduceIte] using decoded.2.2.2.2
  exact aligned_lsu_next_writeback_enabled _ _ _ commit unit write aligned
#print axioms aligned_lsu_next_writeback_enabled
#print axioms aligned_load_writeback_enabled_run
end NutShellProofs
