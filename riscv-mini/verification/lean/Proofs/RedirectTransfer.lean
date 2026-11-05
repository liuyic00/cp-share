import Proofs.FetchRedirect
namespace RiscvMiniProofs
open nCoreSoc

theorem no_branch_mode_not_taken (s : State) (i : Inputs) (mode : v7534 s i = 0) :
    v7759 s i = 0 := by
  simp [v7759, v7758, v7757, v7755, v7754, v7753, v7749,
    v7748, v7747, v7745, v7744, v7743, v7736, v7735, v7734,
    v7733, v7732, v7535, mode, v200, v7521, v26, v716, v29, v22]

theorem redirect_alu (s : State) (i : Inputs) (check : v8475 s i = 1) :
    v7840 s i = 0 := by
  by_cases jump : v8473 s i = 1
  · exact pc_select_alu s i jump
  · apply branch_mode_alu s i
    intro mode
    have no := no_branch_mode_not_taken s i mode
    simp [v8475, v8474, v42, no] at check
    exact jump check

theorem redirect_saved_target (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) (check : v8475 s i = 1) :
    (step s i).g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = v8041 s i := by
  have alu := redirect_alu s i check
  rw [(execute_transfer_step s i reset env).alu, ← circuit_alu_eq]
  simp [v8164, v8163, v7843, v7841, v7842, v725, v7793, alu]

theorem redirect_cancel (s : State) (i : Inputs) (check : v8475 s i = 1) :
    (s.g4.r136_ndut_5Fdpath_5Fstarted ||| v7519 s i) ||| v7759 s i = 1 := by
  rcases BitVec.eq_zero_or_eq_one (v7759 s i) with no | taken
  · have jump : v8473 s i = 1 := by
      simpa [v8475, v8474, v42, no] using check
    rw [fetch_cancel_pc_select, jump]
    simp only [BitVec.reduceEq, ↓reduceIte]
    change (s.g4.r136_ndut_5Fdpath_5Fstarted ||| BitVec.allOnes 1) ||| v7759 s i = BitVec.allOnes 1
    rw [BitVec.or_allOnes, BitVec.allOnes_or]
  · rw [taken]
    exact BitVec.or_allOnes

theorem no_redirect_parts (s : State) (i : Inputs) (check : v8475 s i = 0) :
    v8473 s i ≠ 1 ∧ v7759 s i = 0 := by
  have parts := BitVec.or_eq_zero_iff.mp check
  constructor
  · intro jump
    have first := parts.1
    simp [v8474, v42, jump] at first
  · exact parts.2

theorem cancelled_without_redirect_holds (s : State) (i : Inputs)
    (noReturn : s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst ≠ 268435571)
    (started : s.g4.r136_ndut_5Fdpath_5Fstarted = 0)
    (check : v8475 s i = 0)
    (cancel : (s.g4.r136_ndut_5Fdpath_5Fstarted ||| v7519 s i) ||| v7759 s i ≠ 0) :
    v8473 s i = 2 := by
  have parts := no_redirect_parts s i check
  have zero : v8473 s i ≠ 0 := by
    intro zero
    rw [fetch_cancel_pc_select, zero] at cancel
    simp [started, parts.2] at cancel
  have noSelect := no_legacy_return_select s i noReturn
  have three : v8473 s i ≠ 3 := by
    intro three
    simp [v8487, v155, three] at noSelect
  have bound := (v8473 s i).isLt
  have h0 : (v8473 s i).toNat ≠ 0 := fun h => zero (BitVec.eq_of_toNat_eq h)
  have h1 : (v8473 s i).toNat ≠ 1 := fun h => parts.1 (BitVec.eq_of_toNat_eq h)
  have h3 : (v8473 s i).toNat ≠ 3 := fun h => three (BitVec.eq_of_toNat_eq h)
  apply BitVec.eq_of_toNat_eq
  change (v8473 s i).toNat = 2
  omega

#print axioms redirect_cancel
#print axioms cancelled_without_redirect_holds
#print axioms no_branch_mode_not_taken
#print axioms redirect_alu
#print axioms redirect_saved_target
end RiscvMiniProofs
