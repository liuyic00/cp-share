import Proofs.NonAluBubble
namespace RiscvMiniProofs
open nCoreSoc

private theorem bit_or_one (x : BitVec 1) : x ||| 1#1 = 1#1 := by
  change x ||| BitVec.allOnes 1 = BitVec.allOnes 1
  exact BitVec.or_allOnes
private theorem bit_one_or (x : BitVec 1) : 1#1 ||| x = 1#1 := by
  rw [BitVec.or_comm]
  exact bit_or_one x

-- An enabled non-ALU writeback is paired with a NOP in the execute stage.
def HazardAligned (s : State) : Prop :=
  s.g4.r131_ndut_5Fdpath_5Fwb_5Fsel ≠ 0 →
  s.g4.r132_ndut_5Fdpath_5Fwb_5Fen = 1 →
    s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst = 19

theorem hazard_alignment_reset (s : State) (i : Inputs) (reset : i.nreset = 1) :
    HazardAligned (step s i) := by
  intro _ _
  change v7766 s i = 19
  simp [v7766, v1, v0, reset, v427]

theorem hazard_alignment_step (s : State) (i : Inputs)
    (reset : i.nreset = 0) (trap : v182 s i = 0) :
    HazardAligned (step s i) := by
  intro sel en
  change v8315 s i = 1 at en
  change v8267 s i ≠ 0 at sel
  change v7766 s i = 19
  have stall := no_stall_after_reset s i reset
  have keep : v7774 s i = 0 := by
    simp [v7774, v7773, v7772, stall, trap, v1, v0, reset, v4]
  have advance : v7777 s i = 1 := by
    simp [v7777, v7775, v7776, stall, trap, v4]
  have killed : v7519 s i = 1 := nonalu_decode_kills s i (by
    simpa [v8267, v8266, keep, advance] using sel) (by
    simpa [v8315, v8314, keep, advance] using en)
  simp [v7766, v7765, v7764, v7761, v7760, v7520, killed,
    v7297, stall, v4, v1, v0, reset, v427, bit_or_one, bit_one_or]

theorem hazard_alignment_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles)
    (env : Environment initial inputs) (t : Nat) (ht : cycles ≤ t) :
    HazardAligned (run initial inputs t) := by
  cases t with
  | zero => have := reset.1; omega
  | succ n =>
    change HazardAligned (step (run initial inputs n) (inputs n))
    by_cases hn : cycles ≤ n
    · exact hazard_alignment_step _ _ (reset.2.2 n hn)
        (environment_no_trap _ _ (reset.2.2 n hn) (env n))
    · exact hazard_alignment_reset _ _ (reset.2.1 n (by omega))

theorem forwarding_aligned_port1 (s : State) (i : Inputs)
    (aligned : HazardAligned s) (reset : i.nreset = 0) (trap : v182 s i = 0) :
    v7629 s i = dutRead (step s i) (v7537 s i) := by
  by_cases sel : s.g4.r131_ndut_5Fdpath_5Fwb_5Fsel = 0
  · exact alu_forwarding_port1 s i reset trap sel
  · by_cases en : s.g4.r132_ndut_5Fdpath_5Fwb_5Fen = 1
    · have nop := aligned sel en
      simp [v7629, v7542, v7541, v7539, v7538, v7537, v150,
      dut_read_port1, nop, dutRead]
    · have off : s.g4.r132_ndut_5Fdpath_5Fwb_5Fen = 0 := by
        have bound := s.g4.r132_ndut_5Fdpath_5Fwb_5Fen.isLt
        apply BitVec.eq_of_toNat_eq
        have ne : s.g4.r132_ndut_5Fdpath_5Fwb_5Fen.toNat ≠ 1 := by
          intro h; exact en (BitVec.eq_of_toNat_eq h)
        change s.g4.r132_ndut_5Fdpath_5Fwb_5Fen.toNat = 0
        omega
      rw [dut_read_after_step s i reset]
      by_cases zero : v7537 s i = 0#5
      all_goals simp [v7629, v7542, v7541, v7539, dut_read_port1, v704, v700,
        v699, v697, off, zero, dutRead]


theorem forwarding_aligned_port2 (s : State) (i : Inputs)
    (aligned : HazardAligned s) (reset : i.nreset = 0) (trap : v182 s i = 0) :
    v7725 s i = dutRead (step s i) (v7633 s i) := by
  by_cases sel : s.g4.r131_ndut_5Fdpath_5Fwb_5Fsel = 0
  · exact alu_forwarding_port2 s i reset trap sel
  · by_cases en : s.g4.r132_ndut_5Fdpath_5Fwb_5Fen = 1
    · have nop := aligned sel en
      simp [v7725, v7638, v7637, v7635, v7634, v7633, v150,
      dut_read_port2, nop, dutRead]
    · have off : s.g4.r132_ndut_5Fdpath_5Fwb_5Fen = 0 := by
        have bound := s.g4.r132_ndut_5Fdpath_5Fwb_5Fen.isLt
        apply BitVec.eq_of_toNat_eq
        have ne : s.g4.r132_ndut_5Fdpath_5Fwb_5Fen.toNat ≠ 1 := by
          intro h; exact en (BitVec.eq_of_toNat_eq h)
        change s.g4.r132_ndut_5Fdpath_5Fwb_5Fen.toNat = 0
        omega
      rw [dut_read_after_step s i reset]
      by_cases zero : v7633 s i = 0#5
      all_goals simp [v7725, v7638, v7637, v7635, dut_read_port2, v704, v700,
        v699, v697, off, zero, dutRead]


theorem forwarding_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles)
    (env : Environment initial inputs) (t : Nat) (ht : cycles ≤ t) :
    v7629 (run initial inputs t) (inputs t) =
      dutRead (run initial inputs (t+1)) (v7537 (run initial inputs t) (inputs t)) ∧
    v7725 (run initial inputs t) (inputs t) =
      dutRead (run initial inputs (t+1)) (v7633 (run initial inputs t) (inputs t)) := by
  have aligned := hazard_alignment_reachable initial inputs cycles reset env t ht
  have rst := reset.2.2 t ht
  have trap := environment_no_trap _ _ rst (env t)
  exact ⟨forwarding_aligned_port1 _ _ aligned rst trap,
    forwarding_aligned_port2 _ _ aligned rst trap⟩

#print axioms forwarding_reachable
#print axioms hazard_alignment_reachable
end RiscvMiniProofs
