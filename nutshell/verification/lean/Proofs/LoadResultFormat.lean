import Proofs.LoadShiftCorrespondence
import Proofs.LoadCompletionData
namespace NutShellProofs
open nNutCore
theorem load_mask_1 (x : BitVec 1) : x &&& BitVec.ofNat 1 1 = x := by
  exact BitVec.and_allOnes
theorem load_mask_8 (x : BitVec 8) : x &&& BitVec.ofNat 8 255 = x := by
  exact BitVec.and_allOnes
theorem load_mask_16 (x : BitVec 16) : x &&& BitVec.ofNat 16 65535 = x := by
  exact BitVec.and_allOnes
theorem load_mask_32 (x : BitVec 32) : x &&& BitVec.ofNat 32 4294967295 = x := by
  exact BitVec.and_allOnes
theorem load_lb_result_matches_reference (s r : State) (i j : Inputs)
    (op : v28 s i = MemoryOp.control .lb)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (data : v12412 s i = v16189 r j) : v12460 s i = v16428 r j := by
  have shift : v16423 r j = v16189 r j := rfl
  rw [load_lb_formatted_result s i op outer, data]
  simp [v16428, v16427, v16426, v16425, v16424, v16367, v12415, v12406, shift, BitVec.extractLsb'_and]
  all_goals simp only [load_mask_1, load_mask_8, load_mask_16, load_mask_32]
#print axioms load_lb_result_matches_reference
theorem load_lh_result_matches_reference (s r : State) (i j : Inputs)
    (op : v28 s i = MemoryOp.control .lh)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (data : v12412 s i = v16189 r j) : v12460 s i = v16413 r j := by
  have shift : v16408 r j = v16189 r j := rfl
  rw [load_lh_formatted_result s i op outer, data]
  simp [v16413, v16412, v16411, v16410, v16409, v16353, v12424, v12399, shift, BitVec.extractLsb'_and]
  all_goals simp only [load_mask_1, load_mask_8, load_mask_16, load_mask_32]
#print axioms load_lh_result_matches_reference
theorem load_lw_result_matches_reference (s r : State) (i j : Inputs)
    (op : v28 s i = MemoryOp.control .lw)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (data : v12412 s i = v16189 r j) : v12460 s i = v16392 r j := by
  have shift : v16387 r j = v16189 r j := rfl
  rw [load_lw_formatted_result s i op outer, data]
  simp [v16392, v16391, v16390, v16389, v16388, v16207, v11488, v11103, shift, BitVec.extractLsb'_and]
  all_goals simp only [load_mask_1, load_mask_8, load_mask_16, load_mask_32]
#print axioms load_lw_result_matches_reference
theorem load_lbu_result_matches_reference (s r : State) (i j : Inputs)
    (op : v28 s i = MemoryOp.control .lbu)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (data : v12412 s i = v16189 r j) : v12460 s i = v16370 r j := by
  have shift : v16366 r j = v16189 r j := rfl
  rw [load_lbu_formatted_result s i op outer, data]
  simp [v16370, v12406, v16369, v16368, v16367, shift, BitVec.extractLsb'_and]
  all_goals simp only [load_mask_1, load_mask_8, load_mask_16, load_mask_32]
#print axioms load_lbu_result_matches_reference
theorem load_lhu_result_matches_reference (s r : State) (i j : Inputs)
    (op : v28 s i = MemoryOp.control .lhu)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (data : v12412 s i = v16189 r j) : v12460 s i = v16356 r j := by
  have shift : v16352 r j = v16189 r j := rfl
  rw [load_lhu_formatted_result s i op outer, data]
  simp [v16356, v12399, v16355, v16354, v16353, shift, BitVec.extractLsb'_and]
  all_goals simp only [load_mask_1, load_mask_8, load_mask_16, load_mask_32]
#print axioms load_lhu_result_matches_reference
theorem load_lwu_result_matches_reference (s r : State) (i j : Inputs)
    (op : v28 s i = MemoryOp.control .lwu)
    (outer : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (data : v12412 s i = v16189 r j) : v12460 s i = v16210 r j := by
  have shift : v16206 r j = v16189 r j := rfl
  rw [load_lwu_formatted_result s i op outer, data]
  simp [v16210, v11103, v16209, v16208, v16207, shift, BitVec.extractLsb'_and]
  all_goals simp only [load_mask_1, load_mask_8, load_mask_16, load_mask_32]
#print axioms load_lwu_result_matches_reference
theorem committed_lb_writeback_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory .lb (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (noFault : v11639 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (aligned : v11640 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      v16428 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have op := ((memory_decode_run initial inputs reset t).2 valid .lb matched unit).1
  have outer := original_assumptions_lsu_idle_run initial inputs reset environment t
  have extra := narrow_load_completion_requires_extra_cycle _ _ .lb rfl (by decide) op outer noFault aligned
    (lsu_commit_requires_completion _ _ _ unit commit)
  have data := committed_subword_shifted_data_matches_reference_run initial inputs reset environment t .lb commit unit matched registers extra
  exact (writeback_ordinary_memory_result _ _ _ .lb commit unit op outer).trans
    (load_lb_result_matches_reference _ _ _ _ op outer data)
#print axioms committed_lb_writeback_matches_reference_run
theorem committed_lh_writeback_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory .lh (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (noFault : v11639 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (aligned : v11640 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      v16413 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have op := ((memory_decode_run initial inputs reset t).2 valid .lh matched unit).1
  have outer := original_assumptions_lsu_idle_run initial inputs reset environment t
  have extra := narrow_load_completion_requires_extra_cycle _ _ .lh rfl (by decide) op outer noFault aligned
    (lsu_commit_requires_completion _ _ _ unit commit)
  have data := committed_subword_shifted_data_matches_reference_run initial inputs reset environment t .lh commit unit matched registers extra
  exact (writeback_ordinary_memory_result _ _ _ .lh commit unit op outer).trans
    (load_lh_result_matches_reference _ _ _ _ op outer data)
#print axioms committed_lh_writeback_matches_reference_run
theorem committed_lw_writeback_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory .lw (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (noFault : v11639 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (aligned : v11640 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      v16392 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have op := ((memory_decode_run initial inputs reset t).2 valid .lw matched unit).1
  have outer := original_assumptions_lsu_idle_run initial inputs reset environment t
  have extra := narrow_load_completion_requires_extra_cycle _ _ .lw rfl (by decide) op outer noFault aligned
    (lsu_commit_requires_completion _ _ _ unit commit)
  have data := committed_subword_shifted_data_matches_reference_run initial inputs reset environment t .lw commit unit matched registers extra
  exact (writeback_ordinary_memory_result _ _ _ .lw commit unit op outer).trans
    (load_lw_result_matches_reference _ _ _ _ op outer data)
#print axioms committed_lw_writeback_matches_reference_run
theorem committed_lbu_writeback_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory .lbu (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (noFault : v11639 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (aligned : v11640 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      v16370 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have op := ((memory_decode_run initial inputs reset t).2 valid .lbu matched unit).1
  have outer := original_assumptions_lsu_idle_run initial inputs reset environment t
  have extra := narrow_load_completion_requires_extra_cycle _ _ .lbu rfl (by decide) op outer noFault aligned
    (lsu_commit_requires_completion _ _ _ unit commit)
  have data := committed_subword_shifted_data_matches_reference_run initial inputs reset environment t .lbu commit unit matched registers extra
  exact (writeback_ordinary_memory_result _ _ _ .lbu commit unit op outer).trans
    (load_lbu_result_matches_reference _ _ _ _ op outer data)
#print axioms committed_lbu_writeback_matches_reference_run
theorem committed_lhu_writeback_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory .lhu (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (noFault : v11639 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (aligned : v11640 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      v16356 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have op := ((memory_decode_run initial inputs reset t).2 valid .lhu matched unit).1
  have outer := original_assumptions_lsu_idle_run initial inputs reset environment t
  have extra := narrow_load_completion_requires_extra_cycle _ _ .lhu rfl (by decide) op outer noFault aligned
    (lsu_commit_requires_completion _ _ _ unit commit)
  have data := committed_subword_shifted_data_matches_reference_run initial inputs reset environment t .lhu commit unit matched registers extra
  exact (writeback_ordinary_memory_result _ _ _ .lhu commit unit op outer).trans
    (load_lhu_result_matches_reference _ _ _ _ op outer data)
#print axioms committed_lhu_writeback_matches_reference_run
theorem committed_lwu_writeback_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory .lwu (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (noFault : v11639 (run initial inputs (t + 1)) (inputs (t + 1)) = 0)
    (aligned : v11640 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    v11842 (run initial inputs (t + 2)) (inputs (t + 2)) =
      v16210 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  have valid := commit_requires_execute_valid _ _ _ commit
  have op := ((memory_decode_run initial inputs reset t).2 valid .lwu matched unit).1
  have outer := original_assumptions_lsu_idle_run initial inputs reset environment t
  have extra := narrow_load_completion_requires_extra_cycle _ _ .lwu rfl (by decide) op outer noFault aligned
    (lsu_commit_requires_completion _ _ _ unit commit)
  have data := committed_subword_shifted_data_matches_reference_run initial inputs reset environment t .lwu commit unit matched registers extra
  exact (writeback_ordinary_memory_result _ _ _ .lwu commit unit op outer).trans
    (load_lwu_result_matches_reference _ _ _ _ op outer data)
#print axioms committed_lwu_writeback_matches_reference_run
end NutShellProofs
