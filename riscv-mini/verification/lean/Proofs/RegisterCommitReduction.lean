import Proofs.RegisterFrame
import Proofs.RegisterBridge
namespace RiscvMiniProofs
open nCoreSoc
-- Destination alignment and written value are premises to discharge,
-- not assumptions added to the original environment.
theorem registers_agree_of_destination (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (reset : i.nreset = 0)
    (destination : v1320 s i = 0 ∨ v1320 s i = v701 s i)
    (written : dutRead (step s i) (v701 s i) =
      referenceRead (step s i) (v701 s i)) :
    RegisterAgreement (step s i) := by
  constructor
  · by_cases target : v701 s i = 1#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 1#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x1 s i reset other
      have dut := dut_read_after_step s i reset 1#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x1.trans kept.symm)
  · by_cases target : v701 s i = 2#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 2#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x2 s i reset other
      have dut := dut_read_after_step s i reset 2#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x2.trans kept.symm)
  · by_cases target : v701 s i = 3#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 3#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x3 s i reset other
      have dut := dut_read_after_step s i reset 3#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x3.trans kept.symm)
  · by_cases target : v701 s i = 4#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 4#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x4 s i reset other
      have dut := dut_read_after_step s i reset 4#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x4.trans kept.symm)
  · by_cases target : v701 s i = 5#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 5#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x5 s i reset other
      have dut := dut_read_after_step s i reset 5#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x5.trans kept.symm)
  · by_cases target : v701 s i = 6#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 6#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x6 s i reset other
      have dut := dut_read_after_step s i reset 6#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x6.trans kept.symm)
  · by_cases target : v701 s i = 7#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 7#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x7 s i reset other
      have dut := dut_read_after_step s i reset 7#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x7.trans kept.symm)
  · by_cases target : v701 s i = 8#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 8#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x8 s i reset other
      have dut := dut_read_after_step s i reset 8#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x8.trans kept.symm)
  · by_cases target : v701 s i = 9#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 9#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x9 s i reset other
      have dut := dut_read_after_step s i reset 9#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x9.trans kept.symm)
  · by_cases target : v701 s i = 10#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 10#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x10 s i reset other
      have dut := dut_read_after_step s i reset 10#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x10.trans kept.symm)
  · by_cases target : v701 s i = 11#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 11#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x11 s i reset other
      have dut := dut_read_after_step s i reset 11#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x11.trans kept.symm)
  · by_cases target : v701 s i = 12#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 12#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x12 s i reset other
      have dut := dut_read_after_step s i reset 12#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x12.trans kept.symm)
  · by_cases target : v701 s i = 13#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 13#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x13 s i reset other
      have dut := dut_read_after_step s i reset 13#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x13.trans kept.symm)
  · by_cases target : v701 s i = 14#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 14#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x14 s i reset other
      have dut := dut_read_after_step s i reset 14#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x14.trans kept.symm)
  · by_cases target : v701 s i = 15#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 15#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x15 s i reset other
      have dut := dut_read_after_step s i reset 15#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x15.trans kept.symm)
  · by_cases target : v701 s i = 16#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 16#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x16 s i reset other
      have dut := dut_read_after_step s i reset 16#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x16.trans kept.symm)
  · by_cases target : v701 s i = 17#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 17#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x17 s i reset other
      have dut := dut_read_after_step s i reset 17#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x17.trans kept.symm)
  · by_cases target : v701 s i = 18#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 18#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x18 s i reset other
      have dut := dut_read_after_step s i reset 18#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x18.trans kept.symm)
  · by_cases target : v701 s i = 19#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 19#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x19 s i reset other
      have dut := dut_read_after_step s i reset 19#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x19.trans kept.symm)
  · by_cases target : v701 s i = 20#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 20#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x20 s i reset other
      have dut := dut_read_after_step s i reset 20#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x20.trans kept.symm)
  · by_cases target : v701 s i = 21#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 21#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x21 s i reset other
      have dut := dut_read_after_step s i reset 21#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x21.trans kept.symm)
  · by_cases target : v701 s i = 22#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 22#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x22 s i reset other
      have dut := dut_read_after_step s i reset 22#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x22.trans kept.symm)
  · by_cases target : v701 s i = 23#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 23#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x23 s i reset other
      have dut := dut_read_after_step s i reset 23#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x23.trans kept.symm)
  · by_cases target : v701 s i = 24#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 24#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x24 s i reset other
      have dut := dut_read_after_step s i reset 24#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x24.trans kept.symm)
  · by_cases target : v701 s i = 25#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 25#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x25 s i reset other
      have dut := dut_read_after_step s i reset 25#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x25.trans kept.symm)
  · by_cases target : v701 s i = 26#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 26#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x26 s i reset other
      have dut := dut_read_after_step s i reset 26#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x26.trans kept.symm)
  · by_cases target : v701 s i = 27#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 27#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x27 s i reset other
      have dut := dut_read_after_step s i reset 27#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x27.trans kept.symm)
  · by_cases target : v701 s i = 28#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 28#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x28 s i reset other
      have dut := dut_read_after_step s i reset 28#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x28.trans kept.symm)
  · by_cases target : v701 s i = 29#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 29#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x29 s i reset other
      have dut := dut_read_after_step s i reset 29#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x29.trans kept.symm)
  · by_cases target : v701 s i = 30#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 30#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x30 s i reset other
      have dut := dut_read_after_step s i reset 30#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x30.trans kept.symm)
  · by_cases target : v701 s i = 31#5
    · simpa [target, dutRead, referenceRead] using written
    · have other : v1320 s i ≠ 31#5 := by
        rcases destination with zero | same
        · simp [zero]
        · simpa only [same] using target
      have kept := reference_frame_x31 s i reset other
      have dut := dut_read_after_step s i reset 31#5
      simp [v702, target, dutRead] at dut
      exact dut.trans (agree.x31.trans kept.symm)
theorem register_tasks_of_destination (s : State) (i : Inputs)
    (agree : RegisterAgreement s) (reset : i.nreset = 0)
    (commit : v964 s i = 1)
    (destination : v1320 s i = 0 ∨ v1320 s i = v701 s i)
    (written : dutRead (step s i) (v701 s i) =
      referenceRead (step s i) (v701 s i)) : RegisterTasks s i :=
  (register_tasks_iff_next s i reset commit).mpr
    (registers_agree_of_destination s i agree reset destination written)
#print axioms registers_agree_of_destination
#print axioms register_tasks_of_destination
end RiscvMiniProofs
