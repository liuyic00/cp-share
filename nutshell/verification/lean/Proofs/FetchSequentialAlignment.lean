import Proofs.FetchTargetAlignment
namespace NutShellProofs
open nNutCore

theorem word_alignment_bit1 (x : BitVec 39)
    (aligned : BitVec.extractLsb' 0 2 x = 0) : BitVec.extractLsb' 1 1 x = 0 := by
  have low := congrArg BitVec.toNat aligned
  simp [BitVec.extractLsb'_toNat] at low
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.extractLsb'_toNat, Nat.shiftRight_eq_div_pow]
  omega

/-- Actual sequential fetch arithmetic preserves four-byte alignment. -/
theorem fetch_sequential_target_aligned (s : State) (i : Inputs)
    (aligned : BitVec.extractLsb' 0 2 s.g33.r1065_nfrontend_5Fifu_5Fpc = 0) :
    BitVec.extractLsb' 0 2 (v2749 s i) = 0 := by
  rw [frontend_sequential_address]
  have bit1 := word_alignment_bit1 _ aligned
  simp [bit1, low_add _ _ (by decide : 2 ≤ 39), aligned]

/-- The crossing target latch is constrained only while its valid bit is set. -/
def FetchCrosslineAligned (s : State) : Prop :=
  s.g33.r1066_nfrontend_5Fifu_5FcrosslineJumpLatch = 1 →
    BitVec.extractLsb' 0 2 s.g33.r1067_nfrontend_5Fifu_5FcrosslineJumpTarget = 0

theorem fetch_crossline_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    FetchCrosslineAligned (step s i) := by
  intro valid
  change v9681 s i = 1 at valid
  simp [v9681, v1, v0, reset, v24] at valid

theorem fetch_crossline_alignment_step (s : State) (i : Inputs)
    (old : FetchCrosslineAligned s)
    (prediction : v2739 s i = 1 → BitVec.extractLsb' 0 2 (v2755 s i) = 0) :
    FetchCrosslineAligned (step s i) := by
  intro valid
  change BitVec.extractLsb' 0 2 (v9682 s i) = 0
  by_cases capture : v2739 s i = 1
  · rw [v9682, if_pos capture]
    exact prediction capture
  · rw [v9682, if_neg capture]
    apply old
    change v9681 s i = 1 at valid
    rcases BitVec.eq_zero_or_eq_one (v2739 s i) with zero | one
    · by_cases reset : v1 s i = 1 <;> by_cases update : v9676 s i = 1 <;>
        simp_all [v9681, v9680, v9679, v9678, v24]
    · exact False.elim (capture one)
#print axioms word_alignment_bit1
#print axioms fetch_sequential_target_aligned
#print axioms fetch_crossline_reset
#print axioms fetch_crossline_alignment_step
end NutShellProofs
