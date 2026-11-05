import Std

namespace RiscvMiniProofs

theorem mask_refines {w : Nat} (x mask value narrower : BitVec w)
    (known : x &&& mask = value) (subset : mask &&& narrower = narrower) :
    x &&& narrower = value &&& narrower := by
  calc
    x &&& narrower = (x &&& mask) &&& narrower := by
      rw [BitVec.and_assoc, subset]
    _ = value &&& narrower := by rw [known]

theorem mask_incompatible {w : Nat} (x mask value other pattern : BitVec w)
    (known : x &&& mask = value)
    (different : value &&& other ≠ pattern &&& mask) :
    x &&& other ≠ pattern := by
  intro matched
  apply different
  rw [← known, ← matched]
  ac_rfl

#print axioms mask_incompatible
end RiscvMiniProofs
