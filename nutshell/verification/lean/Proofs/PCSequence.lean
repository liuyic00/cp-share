import Proofs.IssuedPCOrder
namespace NutShellProofs
open nNutCore

def PCSequence (start : BitVec 39) : List (BitVec 39) → BitVec 39 → Prop
  | [], next => start = next
  | pc :: rest, next => pc = start ∧ PCSequence (start + 4) rest next

def SequentialPCs (pcs : List (BitVec 39)) (next : BitVec 39) : Prop :=
  ∃ start, PCSequence start pcs next

theorem sequential_pcs_empty (next : BitVec 39) : SequentialPCs [] next := ⟨next, rfl⟩

theorem sequential_pcs_tail (pcs : List (BitVec 39)) (next : BitVec 39)
    (old : SequentialPCs pcs next) : SequentialPCs pcs.tail next := by
  obtain ⟨start, chain⟩ := old
  cases pcs with
  | nil => exact sequential_pcs_empty next
  | cons pc rest => exact ⟨start + 4, chain.2⟩

theorem pc_sequence_append_next (pcs : List (BitVec 39)) (start next : BitVec 39)
    (old : PCSequence start pcs next) : PCSequence start (pcs ++ [next]) (next + 4) := by
  induction pcs generalizing start with
  | nil => exact ⟨old.symm, congrArg (fun pc => pc + 4) old⟩
  | cons pc rest ih => exact ⟨old.1, ih (start + 4) old.2⟩

theorem sequential_pcs_append_next (pcs : List (BitVec 39)) (next : BitVec 39)
    (old : SequentialPCs pcs next) : SequentialPCs (pcs ++ [next]) (next + 4) := by
  obtain ⟨start, chain⟩ := old
  exact ⟨start, pc_sequence_append_next pcs start next chain⟩

#print axioms sequential_pcs_append_next

theorem temporary_pc32_issued_pcs_sequential (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1)
    (environment : ∀ k, assumes (run initial inputs k) (inputs k))
    (restriction : TemporaryIDUPC32 initial inputs) (t : Nat) :
    SequentialPCs (IssuedPCs (run initial inputs (t + 1)))
      (run initial inputs (t + 1)).g33.r1065_nfrontend_5Fifu_5Fpc := by
  induction t with
  | zero =>
    rw [show run initial inputs (0 + 1) = step initial (inputs 0) from rfl,
      issued_pcs_reset initial (inputs 0) reset]
    exact sequential_pcs_empty _
  | succ t ih =>
    rcases BitVec.eq_zero_or_eq_one (inputs (t + 1)).g0.nreset with noReset | currentReset
    · rcases BitVec.eq_zero_or_eq_one (v14 (run initial inputs (t + 1)) (inputs (t + 1))) with noRedirect | redirect
      · have transition := temporary_pc32_issued_pcs_step initial inputs reset environment restriction t noReset noRedirect
        have pc := temporary_pc32_fetch_pc_transition initial inputs reset environment restriction t
        change SequentialPCs (IssuedPCs (run initial inputs (t + 2))) _
        rw [transition, pc]
        have remaining : SequentialPCs
            (if v11702 (run initial inputs (t + 1)) (inputs (t + 1)) = 1
             then (IssuedPCs (run initial inputs (t + 1))).tail
             else IssuedPCs (run initial inputs (t + 1)))
            (run initial inputs (t + 1)).g33.r1065_nfrontend_5Fifu_5Fpc := by
          split
          · exact sequential_pcs_tail _ _ ih
          · exact ih
        rcases BitVec.eq_zero_or_eq_one (v25943 (run initial inputs (t + 1)) (inputs (t + 1))) with noCapture | capture
        · simpa [noReset, noRedirect, noCapture] using remaining
        · simpa [noReset, noRedirect, capture] using sequential_pcs_append_next _ _ remaining
      · change SequentialPCs (IssuedPCs (step (run initial inputs (t + 1)) (inputs (t + 1)))) _
        rw [issued_pcs_flush _ _ redirect]
        exact sequential_pcs_empty _
    · change SequentialPCs (IssuedPCs (step (run initial inputs (t + 1)) (inputs (t + 1)))) _
      rw [issued_pcs_reset _ _ currentReset]
      exact sequential_pcs_empty _

#print axioms temporary_pc32_issued_pcs_sequential
end NutShellProofs
