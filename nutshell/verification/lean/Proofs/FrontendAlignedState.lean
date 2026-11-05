import Proofs.FrontendNormalState
import Proofs.IDUInstructionPC
namespace NutShellProofs
open nNutCore

def FrontendAlignedState (s : State) : Prop :=
  FrontendBufferNormal s ∧ BitVec.extractLsb' 0 2 s.g33.r1074_nfrontend_5Fibf_5FpcOffsetR = 0

theorem frontend_aligned_state_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    FrontendAlignedState (step s i) := by
  refine ⟨frontend_normal_reset s i reset, ?_⟩
  change BitVec.extractLsb' 0 2 (v10161 s i) = 0
  simp [v10161, v9714, v0, reset, v10140]

/-- No output means neither ordinary offset-advance path is selected. -/
theorem frontend_offset_hold_without_output (s : State) (i : Inputs)
    (normal : FrontendBufferNormal s)
    (retained : BitVec.extractLsb' 0 2 s.g33.r1074_nfrontend_5Fibf_5FpcOffsetR = 0)
    (invalid : v10100 s i = 0) :
    BitVec.extractLsb' 0 2 (step s i).g33.r1074_nfrontend_5Fibf_5FpcOffsetR = 0 := by
  have special := frontend_normal_not_special s i normal
  change BitVec.extractLsb' 0 2 (v10161 s i) = 0
  simp [v10161, v10160, v10159, v10158, v10157, special,
    v10154, v10147, v10112, v10111, v10102, v10101, invalid,
    v10140]
  split
  · rfl
  · exact retained

/-- Original assumptions supply full-width decoding only when output is valid.
Queued PC alignment remains a separate pending invariant. -/
theorem frontend_aligned_state_step (s : State) (i : Inputs)
    (old : FrontendAlignedState s) (environment : assumes s i)
    (queued : BitVec.extractLsb' 0 2 (v9733 s i) = 0) :
    FrontendAlignedState (step s i) := by
  rcases BitVec.eq_zero_or_eq_one i.g0.nreset with reset | reset
  · have selected := frontend_selected_offset_aligned s i queued old.2
    refine ⟨frontend_normal_step s i old.1 selected, ?_⟩
    rcases BitVec.eq_zero_or_eq_one (v10100 s i) with invalid | valid
    · exact frontend_offset_hold_without_output s i old.1 old.2 invalid
    · exact frontend_offset_step_aligned s i old.2 selected
        (original_assumptions_disable_compressed_output s i environment reset valid)
        (frontend_normal_not_special s i old.1)
  · exact frontend_aligned_state_reset s i reset
/-- Empty queue data is irrelevant: require PC alignment only for a valid head. -/
theorem frontend_aligned_state_step_valid_head (s : State) (i : Inputs)
    (old : FrontendAlignedState s) (environment : assumes s i)
    (queued : v9802 s i = 1 → BitVec.extractLsb' 0 2 (v9733 s i) = 0) :
    FrontendAlignedState (step s i) := by
  rcases BitVec.eq_zero_or_eq_one (v9802 s i) with empty | valid
  · refine ⟨frontend_normal_step_empty s i old.1 empty, ?_⟩
    apply frontend_offset_hold_without_output s i old.1 old.2
    simp [v10100, v10099, empty]
  · exact frontend_aligned_state_step s i old environment (queued valid)
#print axioms frontend_aligned_state_step_valid_head
#print axioms frontend_aligned_state_reset
#print axioms frontend_offset_hold_without_output
#print axioms frontend_aligned_state_step
end NutShellProofs
