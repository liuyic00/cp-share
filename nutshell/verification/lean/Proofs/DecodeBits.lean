import Proofs.PipelineCapture
namespace NutShellProofs
open nNutCore

theorem opcode_of_mask (x mask value : BitVec w)
    (lowMask : BitVec.extractLsb' 0 7 mask = BitVec.allOnes 7)
    (matched : value = x &&& mask) :
    BitVec.extractLsb' 0 7 x = BitVec.extractLsb' 0 7 value := by
  have low := congrArg (BitVec.extractLsb' 0 7) matched
  simpa only [BitVec.extractLsb'_and, lowMask, BitVec.and_allOnes] using low.symm

theorem low_opcode_mask (x : BitVec 64) (opcode : BitVec 7)
    (low : BitVec.extractLsb' 0 7 x = opcode) :
    opcode.setWidth 64 = x &&& (BitVec.allOnes 7).setWidth 64 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k
  have bit := congrArg (fun y : BitVec 7 => y.getLsbD k) low
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_extractLsb',
    BitVec.getLsbD_and, BitVec.getLsbD_allOnes] at bit ⊢
  by_cases small : k < 7
  · have bound : k < 64 := by omega
    simpa [small, bound] using bit.symm
  · have zero : opcode.getLsbD k = false := by simpa [small] using bit.symm
    simp [small, zero]

#print axioms low_opcode_mask
/-- Two masked instruction matches cannot overlap when shared bits disagree. -/
theorem instruction_masks_incompatible (x a b c e : BitVec w)
    (different : b &&& c ≠ e &&& a) (first : x &&& a = b) :
    e ≠ x &&& c := by
  intro second
  apply different
  calc
    b &&& c = (x &&& a) &&& c := congrArg (fun v => v &&& c) first.symm
    _ = (x &&& c) &&& a := by ac_rfl
    _ = e &&& a := congrArg (fun v => v &&& a) second.symm

end NutShellProofs
