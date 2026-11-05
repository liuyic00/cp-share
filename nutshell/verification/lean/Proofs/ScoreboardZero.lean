import Proofs.IssueReadiness
namespace NutShellProofs
open nNutCore

def ScoreboardZeroFree (s : State) : Prop :=
  BitVec.extractLsb' 0 1 s.g40.r1285_nbackend_5Fisu_5Fbusy = 0

theorem scoreboard_zero_step (s : State) (i : Inputs) :
    ScoreboardZeroFree (step s i) := by
  change BitVec.extractLsb' 0 1 (v11813 s i) = 0
  unfold v11813
  split
  · simp [v11103]
  · unfold v11812
    split
    · simp [v11103]
    · change BitVec.setWidth 1 (v11810 s i ++ (0 : BitVec 1)) = 0
      rw [BitVec.setWidth_append (x := v11810 s i) (y := (0 : BitVec 1)) (k := 1)]
      rfl

theorem scoreboard_zero_run (initial : State) (inputs : Nat → Inputs) (t : Nat) :
    ScoreboardZeroFree (run initial inputs (t + 1)) :=
  scoreboard_zero_step _ _

theorem source_1_zero_not_busy (s : State) (i : Inputs)
    (zero : ScoreboardZeroFree s) (addr : v11723 s i = 0) : v11726 s i = 0 := by
  simpa [v11726, v11725, v11724, v11710, addr] using zero

theorem source_2_zero_not_busy (s : State) (i : Inputs)
    (zero : ScoreboardZeroFree s) (addr : v11765 s i = 0) : v11768 s i = 0 := by
  simpa [v11768, v11767, v11766, v11710, addr] using zero

#print axioms scoreboard_zero_step
end NutShellProofs
