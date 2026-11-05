import Proofs.LoadRegisterStep
import Proofs.MemoryAlignmentCorrespondence
namespace NutShellProofs
open nNutCore
theorem reference_load_alignment_flags (s : State) (i : Inputs) (operation : MemoryOp)
    (load : operation.isLoad = true) :
    referenceLoadAligned operation s i ↔ BitVec.extractLsb' 0 operation.alignmentBits (v15632 s i + v16164 s i) = 0 := by
  cases operation <;>
    simp_all [referenceLoadAligned, MemoryOp.isLoad, MemoryOp.alignmentBits, v16398, v16397, v16396, v16395, v16393, v24, v16394, v16377, v16375, v16374, v16373, v16371, v16372, v16376, v16170, v16168, v16167, v16166, v15770, v16165, v16169, v16342, v16341, v16340, v16339, v16337, v16338, v16196, v16194, v16193, v16192, v16190, v16191, v16195, low_add _ _ (by decide : 64 ≤ 65), BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 64 ≤ 64)]
#print axioms reference_load_alignment_flags
end NutShellProofs
