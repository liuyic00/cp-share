import Proofs.LoadSubwordAddressRun
namespace NutShellProofs
open nNutCore

theorem load_byte_selection_is_shift (s : State) (i : Inputs) :
    v12412 s i = (s.g41.r1339_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FrdataLatch).ushiftRight
      ((v12359 s i).toNat * 8) := by
  have cases : ∀ x : BitVec 3, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 := by decide
  rcases cases (v12359 s i) with h | h | h | h | h | h | h | h
  · rw [load_byte_offset_0 s i h, h]
    simp
  · rw [load_byte_offset_1 s i h, h]
    simpa using (BitVec.ushiftRight_eq_extractLsb'_of_lt (x := s.g41.r1339_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FrdataLatch) (by decide : 8 < 64)).symm
  · rw [load_byte_offset_2 s i h, h]
    simpa using (BitVec.ushiftRight_eq_extractLsb'_of_lt (x := s.g41.r1339_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FrdataLatch) (by decide : 16 < 64)).symm
  · rw [load_byte_offset_3 s i h, h]
    simpa using (BitVec.ushiftRight_eq_extractLsb'_of_lt (x := s.g41.r1339_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FrdataLatch) (by decide : 24 < 64)).symm
  · rw [load_byte_offset_4 s i h, h]
    simpa using (BitVec.ushiftRight_eq_extractLsb'_of_lt (x := s.g41.r1339_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FrdataLatch) (by decide : 32 < 64)).symm
  · rw [load_byte_offset_5 s i h, h]
    simpa using (BitVec.ushiftRight_eq_extractLsb'_of_lt (x := s.g41.r1339_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FrdataLatch) (by decide : 40 < 64)).symm
  · rw [load_byte_offset_6 s i h, h]
    simpa using (BitVec.ushiftRight_eq_extractLsb'_of_lt (x := s.g41.r1339_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FrdataLatch) (by decide : 48 < 64)).symm
  · rw [load_byte_offset_7 s i h, h]
    simpa using (BitVec.ushiftRight_eq_extractLsb'_of_lt (x := s.g41.r1339_nbackend_5Fexu_5Flsu_5FlsExecUnit_5FrdataLatch) (by decide : 56 < 64)).symm

theorem reference_load_shift (s : State) (i : Inputs) :
    v16189 s i = (v16181 s i).ushiftRight ((v16186 s i).toNat * 8) := by
  have cases : ∀ x : BitVec 3, x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 6 ∨ x = 7 := by decide
  rcases cases (v16186 s i) with h | h | h | h | h | h | h | h <;>
    simp [v16189, v16188, v16187, v11483, v2687, h]
#print axioms load_byte_selection_is_shift
#print axioms reference_load_shift
theorem committed_subword_shifted_data_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k)) (t : Nat)
    (operation : MemoryOp)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (registers : ArchitecturalRegistersAligned (run initial inputs (t + 2)))
    (extra : (run initial inputs (t + 1)).g41.r1334_nbackend_5Fexu_5Flsu_5FlsExecUnit_5Fstate = 3) :
    v12412 (run initial inputs (t + 1)) (inputs (t + 1)) =
      v16189 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  rw [load_byte_selection_is_shift, reference_load_shift,
    committed_subword_reference_data_run initial inputs reset environment t commit unit extra,
    committed_subword_byte_offset_matches_reference_run initial inputs reset environment t operation commit unit matched registers extra]
#print axioms committed_subword_shifted_data_matches_reference_run
end NutShellProofs
