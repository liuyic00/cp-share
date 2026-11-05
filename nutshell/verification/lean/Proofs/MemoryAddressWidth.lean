import Proofs.LoadAddressCorrespondence
namespace NutShellProofs
open nNutCore

theorem original_memory_address_upper_zero (s : State) (i : Inputs)
    (environment : assumes s i) (reset : i.g0.nreset = 0) :
    BitVec.extractLsb' 38 26 (v11612 s i) = 0 := by
  have all : (assumptionChecks0 s i).all id = true := environment
  simp only [assumptionChecks0, List.all_cons, List.all_nil, Bool.and_eq_true,
    Bool.true_and, Bool.and_true] at all
  have check : v31102 s i ≠ 1 ∨ v31101 s i = 1 := of_decide_eq_true all.2.1
  have gate : v31102 s i = 1 := by
    simp [v31102, v12235, v12234, v12103, v11455, reset, v24]
  have enabled := check.resolve_left (not_not_intro gate)
  simpa [v31101, v31099, v31100] using enabled

theorem sign_extend_address_low39 (address : BitVec 64)
    (upper : BitVec.extractLsb' 38 26 address = 0) :
    (BitVec.extractLsb' 0 39 address).signExtend 64 = address := by
  have high (bit : Nat) (lo : 38 ≤ bit) (hi : bit < 64) : address.getLsbD bit = false := by
    have eq := congrArg (fun x : BitVec 26 => x.getLsbD (bit - 38)) upper
    have bound : bit - 38 < 26 := by omega
    have index : 38 + (bit - 38) = bit := by omega
    simpa [BitVec.getLsbD_extractLsb', bound, index] using eq
  have sign : (BitVec.extractLsb' 0 39 address).msb = false := by
    simpa [BitVec.msb_eq_getLsbD_last, BitVec.getLsbD_extractLsb'] using high 38 (by decide) (by decide)
  apply BitVec.eq_of_getLsbD_eq
  intro bit inRange
  rw [BitVec.getLsbD_signExtend]
  by_cases low : bit < 39
  · simp [low, inRange, BitVec.getLsbD_extractLsb']
  · have lo : 38 ≤ bit := by omega
    simp only [low, inRange, sign, ↓reduceIte]
    exact (high bit lo inRange).symm

#print axioms original_memory_address_upper_zero
#print axioms sign_extend_address_low39
theorem load_address_extended_matches_reference_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (t : Nat) (operation : MemoryOp) (load : operation.isLoad = true)
    (commit : v9 (run initial inputs (t + 2)) (inputs (t + 2)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (matched : IsMemory operation (EXUPair (run initial inputs (t + 1))).1)
    (aligned : ArchitecturalRegistersAligned (run initial inputs (t + 2))) :
    (BitVec.extractLsb' 0 39 (v11612 (run initial inputs (t + 1)) (inputs (t + 1)))).signExtend 64 =
      v24059 (run initial inputs (t + 2)) (inputs (t + 2)) := by
  exact (sign_extend_address_low39 _ (original_memory_address_upper_zero _ _
    (environment (t + 1)) (next_commit_controls _ _ _ commit).1)).trans
      (load_address_matches_reference_node_run initial inputs reset environment t operation load commit unit matched aligned)
#print axioms load_address_extended_matches_reference_run
end NutShellProofs
