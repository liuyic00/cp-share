import Proofs.ScoreboardBits
namespace NutShellProofs
open nNutCore

theorem scoreboard_update (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (flush : v11458 s i = 0) :
    (step s i).g40.r1285_nbackend_5Fisu_5Fbusy =
      (BitVec.extractLsb' 1 31 (v11809 s i)) ++ (0 : BitVec 1) := by
  change v11813 s i = _
  simp [v11813, v11456, v11455, reset, v11812, flush, v11811, v11810, v24]

theorem scoreboard_issue_sets (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (flush : v11458 s i = 0)
    (fire : v24283 s i = 1) (nonzero : v11803 s i ≠ 0) :
    (step s i).g40.r1285_nbackend_5Fisu_5Fbusy.getLsbD (v11803 s i).toNat = true := by
  have set : v11789 s i = 1 := by
    change v11705 s i &&& v11788 s i = 1
    rw [BitVec.and_comm]
    exact fire
  have mask : v11808 s i = registerMask (v11803 s i) := by
    simp [v11808, set, v11806, v11805, v11804, v11790, v11483, registerMask]
  rw [scoreboard_update s i reset flush, clear_zero_preserves_bit _ _ nonzero]
  change (v11490 s i ||| v11808 s i).getLsbD (v11803 s i).toNat = true
  rw [BitVec.getLsbD_or, mask, register_mask_hit]
  simp

theorem scoreboard_clear_avoids_execute (s : State) (i : Inputs)
    (validWrite : v11478 s i = 1) (nonzero : v11470 s i ≠ 0) :
    (v11487 s i).getLsbD (v11470 s i).toNat = false := by
  by_cases same : v11465 s i = v11470 s i
  · have destNonzero : v11465 s i ≠ 0 := fun h => nonzero (same.symm.trans h)
    have depend : v11479 s i = 1 := by
      simp only [v11479, v11472, v11467, v11466, v11471]
      have nz : v11465 s i ≠ BitVec.ofNat 5 0 := destNonzero
      rw [if_pos nz, if_pos same, validWrite]
      rfl
    simp [v11487, v11481, v11480, depend, v24, v11103]
  · by_cases clear : v11481 s i = 1
    · rw [v11487, if_pos clear]
      exact register_mask_miss _ _ same
    · rw [v11487, if_neg clear]
      simp [v11103]

theorem scoreboard_execute_preserved (s : State) (i : Inputs)
    (reset : i.g0.nreset = 0) (flush : v11458 s i = 0)
    (validWrite : v11478 s i = 1) (nonzero : v11470 s i ≠ 0)
    (busy : s.g40.r1285_nbackend_5Fisu_5Fbusy.getLsbD (v11470 s i).toNat = true) :
    (step s i).g40.r1285_nbackend_5Fisu_5Fbusy.getLsbD (v11470 s i).toNat = true := by
  rw [scoreboard_update s i reset flush, clear_zero_preserves_bit _ _ nonzero]
  change ((s.g40.r1285_nbackend_5Fisu_5Fbusy &&&
    (v11487 s i ^^^ BitVec.allOnes 32)) ||| v11808 s i).getLsbD (v11470 s i).toNat = true
  rw [BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_xor,
    scoreboard_clear_avoids_execute s i validWrite nonzero, busy, BitVec.getLsbD_allOnes]
  simp [show (v11470 s i).toNat < 32 from (v11470 s i).isLt]

#print axioms scoreboard_issue_sets
#print axioms scoreboard_execute_preserved
end NutShellProofs
