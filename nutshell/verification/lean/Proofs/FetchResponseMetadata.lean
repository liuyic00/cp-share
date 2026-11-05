import Proofs.TemporaryFetchSequence
namespace NutShellProofs
open nNutCore

/-- A redirect can capture metadata in idle state, but cannot start its request. -/
theorem redirected_fetch_capture_stays_idle (s : State) (i : Inputs)
    (capture : v25943 s i = 1) (redirect : v14 s i = 1) :
    (step s i).g51.r1643_nio_5Fimem_5Fcache_5Fstate = 0 := by
  have idle : s.g51.r1643_nio_5Fimem_5Fcache_5Fstate = 0 := by
    by_cases idle : s.g51.r1643_nio_5Fimem_5Fcache_5Fstate = BitVec.ofNat 3 0
    · exact idle
    · simp [v25943, v2689, v2688, v2687, idle] at capture
  have stopped : v25817 s i = 0 := by
    simp [v25817, v25816, v25815, v25814, v25813, v25812, v25811,
      v25810, v19, v18, v17, redirect, v15, v24, v2750]
  change v25883 s i = 0
  simp [v25883, v25882, v25804, idle, v2687, v25839, v25818, stopped]

def SequentialFetchMetadata (metadata : BitVec 87) : Prop :=
  ∃ pc : BitVec 39, metadata = (0 : BitVec 5) ++ (((8 : BitVec 4) ++ (pc + 4)) ++ pc)

def ActiveFetchMetadataSequential (s : State) : Prop :=
  s.g51.r1643_nio_5Fimem_5Fcache_5Fstate ≠ 0 →
    SequentialFetchMetadata s.g51.r1656_nio_5Fimem_5Fcache_5Fmemuser

theorem active_fetch_metadata_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    ActiveFetchMetadataSequential (step s i) := by
  intro active
  change v25883 s i ≠ 0 at active
  simp [v25883, v25803, reset, v2687] at active

theorem active_fetch_metadata_step (s : State) (i : Inputs)
    (old : ActiveFetchMetadataSequential s)
    (source : v25943 s i = 1 → v14 s i = 0 → SequentialFetchMetadata (v25965 s i)) :
    ActiveFetchMetadataSequential (step s i) := by
  intro active
  change SequentialFetchMetadata (v25966 s i)
  by_cases capture : v25943 s i = 1
  · rw [v25966, if_pos capture]
    have noRedirect : v14 s i = 0 := by
      rcases BitVec.eq_zero_or_eq_one (v14 s i) with zero | one
      · exact zero
      · exact False.elim (active (redirected_fetch_capture_stays_idle s i capture one))
    exact source capture noRedirect
  · rw [v25966, if_neg capture]
    apply old
    intro idle
    have noRequest : v25808 s i ≠ 1 := by
      intro requested
      apply capture
      simp [v25943, v2689, v2688, idle, v2687, requested]
    have noStart : v25818 s i = 0 := by
      rcases BitVec.eq_zero_or_eq_one (v25808 s i) with zero | one
      · simp [v25818, v25809, zero]
      · exact False.elim (noRequest one)
    change v25883 s i ≠ 0 at active
    simp [v25883, v25882, v25804, idle, v2687, v25839, noStart] at active

theorem temporary_pc32_active_fetch_metadata_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) :
    ActiveFetchMetadataSequential (run initial inputs (t + 1)) := by
  induction t with
  | zero => exact active_fetch_metadata_reset _ _ reset
  | succ t ih =>
    apply active_fetch_metadata_step _ _ ih
    intro capture noRedirect
    exact ⟨_, temporary_pc32_accepted_fetch_metadata initial inputs reset environment restriction t capture noRedirect⟩

/-- The actual enqueue buses retain successor PC and sequential branch flags. -/
theorem fetch_enqueue_sequential_metadata (s : State) (i : Inputs)
    (metadata : ActiveFetchMetadataSequential s) (enqueue : v10241 s i = 1) :
    v10273 s i = v10265 s i + 4 ∧ v10501 s i = 8 := by
  obtain ⟨pc, encoded⟩ := metadata (fetch_enqueue_requires_active_response s i enqueue)
  have data : v10262 s i = ((8 : BitVec 4) ++ (pc + 4)) ++ pc := by
    simp [v10262, v10261, v10260, v10259, v10258, v10257, encoded,
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 82 ≤ 82)]
  constructor
  · simp only [v10273, v10272, v10271, v10265, v10264, v10263, data,
      BitVec.extractLsb'_append_eq_of_le (by decide : 39 ≤ 39), Nat.sub_self,
      BitVec.extractLsb'_append_eq_of_add_le (by decide : 0 + 39 ≤ 39),
      BitVec.extractLsb'_eq_self]
  · simp only [v10501, v10500, v10499, data,
      BitVec.extractLsb'_append_eq_of_le (by decide : 39 ≤ 78)]
    change BitVec.extractLsb' 39 4 ((8 : BitVec 4) ++ (pc + 4)) = 8
    rw [BitVec.extractLsb'_append_eq_of_le (by decide : 39 ≤ 39)]
    rfl

theorem temporary_pc32_fetch_enqueue_metadata_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat)
    (enqueue : v10241 (run initial inputs (t + 1)) (inputs (t + 1)) = 1) :
    v10273 (run initial inputs (t + 1)) (inputs (t + 1)) =
      v10265 (run initial inputs (t + 1)) (inputs (t + 1)) + 4 ∧
    v10501 (run initial inputs (t + 1)) (inputs (t + 1)) = 8 :=
  fetch_enqueue_sequential_metadata _ _
    (temporary_pc32_active_fetch_metadata_run initial inputs reset environment restriction t) enqueue

#print axioms temporary_pc32_fetch_enqueue_metadata_run
#print axioms redirected_fetch_capture_stays_idle
#print axioms temporary_pc32_active_fetch_metadata_run
end NutShellProofs
