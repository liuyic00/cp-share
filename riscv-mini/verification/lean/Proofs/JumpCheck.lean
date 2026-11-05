import Proofs.ExecuteTransfer
import Proofs.MaskFacts
import Proofs.TrapFacts
namespace RiscvMiniProofs
open nCoreSoc

-- For jumps the saved PC check must accompany the saved instruction.
def JumpChecked (s : State) : Prop :=
  (s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111 ∨
   s.g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) →
  s.g4.r135_ndut_5Fdpath_5Fpc_5Fcheck = 1

theorem jump_checked_reset (s : State) (i : Inputs) (reset : i.nreset = 1) :
    JumpChecked (step s i) := by
  intro known
  change (v7780 s i &&& 127 = 111 ∨ v7780 s i &&& 28799 = 103) at known
  simp only [v7780, v1, v0, reset, v427] at known
  simp at known

private theorem jump_check_execute (s : State) (i : Inputs)
    (known : s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst &&& 127 = 111 ∨
      s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst &&& 28799 = 103) : v8474 s i = 1 := by
  rcases known with jal | jalr
  · have notlui := mask_incompatible _ 127 111 127 55 jal (by decide)
    have notauipc := mask_incompatible _ 127 111 127 23 jal (by decide)
    change s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst &&& 127#32 = 111#32 at jal
    change s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst &&& 127#32 ≠ 55#32 at notlui
    change s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst &&& 127#32 ≠ 23#32 at notauipc
    simp only [v8474, v8473, v8472, v8471, v8470, v8469,
      v7303, v7302, v7301, v7300, v7299, v7298,
      v7307, v7306, v7305, v7304, v7311, v7310, v7309, v7308,
      v42, jal, Ne.symm notlui, Ne.symm notauipc, BitVec.reduceEq, ↓reduceIte]
  · have notlui := mask_incompatible _ 28799 103 127 55 jalr (by decide)
    have notauipc := mask_incompatible _ 28799 103 127 23 jalr (by decide)
    have notjal := mask_incompatible _ 28799 103 127 111 jalr (by decide)
    change s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst &&& 28799#32 = 103#32 at jalr
    change s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst &&& 127#32 ≠ 55#32 at notlui
    change s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst &&& 127#32 ≠ 23#32 at notauipc
    change s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst &&& 127#32 ≠ 111#32 at notjal
    simp only [v8474, v8473, v8472, v8471, v8470, v8469, v8468,
      v7303, v7302, v7301, v7300, v7299, v7298,
      v7307, v7306, v7305, v7304, v7311, v7310, v7309, v7308,
      v7315, v7314, v7313, v7312, v42, jalr,
      Ne.symm notlui, Ne.symm notauipc, Ne.symm notjal, BitVec.reduceEq, ↓reduceIte]

theorem jump_checked_step (s : State) (i : Inputs)
    (reset : i.nreset = 0) (env : assumes s i) : JumpChecked (step s i) := by
  intro known
  have inst := (execute_transfer_step s i reset env).instruction
  change ((step s i).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111 ∨
    (step s i).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) at known
  rw [inst] at known
  have checked := jump_check_execute s i known
  have trap := environment_no_trap s i reset env
  have stall := no_stall_after_reset s i reset
  change v8477 s i = 1
  simp [v8477, v8476, v8475, v7774, v7773, v7772, v7777, v7776, v7775,
    v1, v0, v4, reset, trap, stall, checked]
  exact BitVec.allOnes_or

theorem jump_checked_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) : JumpChecked (run initial inputs t) := by
  cases t with
  | zero => have := reset.1; omega
  | succ n =>
    by_cases hn : cycles ≤ n
    · exact jump_checked_step _ _ (reset.2.2 n hn) (env n)
    · exact jump_checked_reset _ _ (reset.2.1 n (by omega))

theorem jump_target_bit_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t)
    (known : (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 127 = 111 ∨
      (run initial inputs t).g3.r125_ndut_5Fdpath_5Few_5Freg_5F_5Finst &&& 28799 = 103) :
    BitVec.extractLsb' 1 1 (run initial inputs t).g3.r127_ndut_5Fdpath_5Few_5Freg_5F_5Falu = 0 :=
  environment_pc_bit _ _ (reset.2.2 t ht) (env t)
    (jump_checked_reachable initial inputs cycles reset env t ht known)

#print axioms jump_target_bit_reachable
#print axioms jump_checked_reachable
end RiscvMiniProofs
