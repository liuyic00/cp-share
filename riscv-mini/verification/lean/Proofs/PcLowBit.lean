import Proofs.ReturnExclusion
namespace RiscvMiniProofs
open nCoreSoc

structure PcLowBit (s : State) : Prop where
  fetch : s.g4.r137_ndut_5Fdpath_5Fpc.getLsbD 0 = false
  execute : s.g3.r124_ndut_5Fdpath_5Ffe_5Freg_5Fpc.getLsbD 0 = false
  writeback : s.g3.r126_ndut_5Fdpath_5Few_5Freg_5F_5Fpc.getLsbD 0 = false

theorem pc_low_bit_reset (s : State) (i : Inputs) (reset : i.nreset = 1) :
    PcLowBit (step s i) := by
  constructor
  · change (v8508 s i).getLsbD 0 = false
    simp [v8508, v1, v0, reset, v8478]
  · change (v7771 s i).getLsbD 0 = false
    simp [v7771, v7770, v1, v0, reset, v7767]
  · change (v7783 s i).getLsbD 0 = false
    simp [v7783, v1, v0, reset, v3]

theorem pc_low_bit_step (s : State) (i : Inputs) (low : PcLowBit s)
    (reset : i.nreset = 0) (env : assumes s i)
    (noReturn : s.g3.r123_ndut_5Fdpath_5Ffe_5Freg_5Finst ≠ 268435571) :
    PcLowBit (step s i) := by
  have trap := environment_no_trap s i reset env
  have stall := no_stall_after_reset s i reset
  have noSelect := no_legacy_return_select s i noReturn
  have fetchBit : s.g4.r137_ndut_5Fdpath_5Fpc[0] = false := by simpa using low.fetch
  have executeBit : s.g3.r124_ndut_5Fdpath_5Ffe_5Freg_5Fpc[0] = false := by simpa using low.execute
  have sequential : (v8502 s i).getLsbD 0 = false := by
    simp [v8502, v8501, v8500, v8499, v4, BitVec.getElem_add,
      BitVec.getElem_append (n := 1) (m := 33), fetchBit]
  have target : (v8497 s i).getLsbD 0 = false := by
    simp [v8497, v8496, BitVec.getElem_shiftLeft]
  constructor
  · change (v8508 s i).getLsbD 0 = false
    simp only [v8508, v8507, v8506, v8505, v1, v0, reset, trap, stall, noSelect,
      BitVec.reduceEq, ↓reduceIte, v8504, v8503]
    split
    · exact target
    · split
      · exact low.fetch
      · exact sequential
  · change (v7771 s i).getLsbD 0 = false
    simp only [v7771, v7770, v1, v0, reset, BitVec.reduceEq, ↓reduceIte, v7769]
    split
    · simpa using low.fetch
    · simp [v7768, v4, BitVec.getElem_append (n := 1) (m := 32), executeBit]
  · rw [(execute_transfer_step s i reset env).pc]
    exact low.execute

theorem pc_low_bit_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (env : Environment initial inputs)
    (t : Nat) (ht : cycles ≤ t) : PcLowBit (run initial inputs t) := by
  induction t with
  | zero => have := reset.1; omega
  | succ n ih =>
    by_cases hn : cycles ≤ n
    · exact pc_low_bit_step _ _ (ih hn) (reset.2.2 n hn) (env n)
        (fetch_excludes_legacy_return initial inputs cycles reset env n hn)
    · exact pc_low_bit_reset _ _ (reset.2.1 n (by omega))

#print axioms pc_low_bit_reachable
end RiscvMiniProofs
