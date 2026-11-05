import Proofs.ReferenceConfig
import Proofs.ReferenceExecution
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedSimpArgs false

-- These are the actual reference-model jump cones, before decoding the
-- instruction immediate and proving target alignment against the DUT.
theorem reference_jal_target (s : State) (i : Inputs) :
    v2235 s i = v2222 s i + v2092 s i := by
  change refExec_v2303 (v2222 s i) (v2092 s i) = _
  exact reference_execution_add _ _

theorem reference_jalr_sum (s : State) (i : Inputs) :
    v2203 s i = v1721 s i + v2092 s i := by
  change refExec_v2303 (v1721 s i) (v2092 s i) = _
  exact reference_execution_add _ _

theorem reference_jal_link (s : State) (i : Inputs) :
    v2255 s i = v2222 s i + 4 := by
  change BitVec.extractLsb' 0 32 (((0#1) ++ v2222 s i) + (4#33)) = _
  rw [show (4#33) = (0#1) ++ (4#32) by decide]
  exact reference_execution_add _ _

theorem reference_jalr_link (s : State) (i : Inputs) :
    v2226 s i = v2222 s i + 4 :=
  reference_jal_link s i

theorem reference_jalr_target (s : State) (i : Inputs) :
    v2205 s i = (BitVec.extractLsb' 1 31 (v1721 s i + v2092 s i)) ++ (0#1) := by
  simp only [v2205, v2204, reference_jalr_sum, v4]

theorem reference_jal_alignment (s : State) (i : Inputs) (config : ReferenceConfig s) :
    v2249 s i = 1 ↔ BitVec.extractLsb' 0 2 (v2222 s i + v2092 s i) = 0 := by
  simp [v2249, v2248, v2247, v2244, v2243, v2239, v2242, v2241, v2240,
    v2231, v2230, v2229, v2228, v2227, v2194, config.misa, v512, v38, v155,
    reference_jal_target]

theorem reference_jalr_alignment (s : State) (i : Inputs) (config : ReferenceConfig s) :
    v2219 s i = 1 ↔ BitVec.extractLsb' 0 2 (v2205 s i) = 0 := by
  simp [v2219, v2218, v2217, v2214, v2213, v2209, v2212, v2211, v2210,
    v2199, v2198, v2197, v2196, v2195, v2194, config.misa, v512, v38, v155]

#print axioms reference_jal_target
#print axioms reference_jal_link
#print axioms reference_jalr_target
#print axioms reference_jal_alignment
#print axioms reference_jalr_alignment
end RiscvMiniProofs
