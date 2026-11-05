import Proofs.Contract
set_option linter.unusedVariables false
namespace NutShellProofs
open nNutCore
def internal1_v31093 (inst : BitVec 64) (valid : BitVec 1) (enable : BitVec 1) : BitVec 2 := BitVec.extractLsb' 0 2 inst
def internal1_v2750 (inst : BitVec 64) (valid : BitVec 1) (enable : BitVec 1) : BitVec 2 := BitVec.ofNat 2 3
def internal1_v31094 (inst : BitVec 64) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := if (internal1_v31093 inst valid enable) = (internal1_v2750 inst valid enable) then 1 else 0
def internal1_v12192 (inst : BitVec 64) (valid : BitVec 1) (enable : BitVec 1) : BitVec 2 := BitVec.extractLsb' 0 2 inst
def internal1_v12193 (inst : BitVec 64) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := if (internal1_v12192 inst valid enable) ≠ (internal1_v2750 inst valid enable) then 1 else 0
def internal1_v31095 (inst : BitVec 64) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := ((internal1_v31094 inst valid enable) ||| (internal1_v12193 inst valid enable))
def internal1_v24 (inst : BitVec 64) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := BitVec.ofNat 1 0
def internal1_v31096 (inst : BitVec 64) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := if valid = (internal1_v24 inst valid enable) then 1 else 0
def internal1_v31097 (inst : BitVec 64) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := ((internal1_v31095 inst valid enable) ||| (internal1_v31096 inst valid enable))
def internal1_check (inst : BitVec 64) (valid : BitVec 1) (enable : BitVec 1) : Prop := enable ≠ 1 ∨ (internal1_v31097 inst valid enable) = 1
theorem internal1_tautology (inst : BitVec 64) (valid : BitVec 1) (enable : BitVec 1) : internal1_check inst valid enable := by
  simp only [internal1_check, internal1_v31093, internal1_v2750, internal1_v31094, internal1_v12192, internal1_v12193, internal1_v31095, internal1_v24, internal1_v31096, internal1_v31097]
  bv_decide
theorem task_1_always (s : State) (i : Inputs) : TaskHolds 1 s i := by
  change decide ((v31098 s i) ≠ 1 ∨ (v31097 s i) = 1) = true
  apply decide_eq_true
  change internal1_check (v12191 s i) (v12140 s i) (v31098 s i)
  exact internal1_tautology _ _ _
#print axioms task_1_always
def internal2_v11527 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := BitVec.extractLsb' 5 1 op
def internal2_v11528 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := (valid &&& (internal2_v11527 op valid enable))
def internal2_v24 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := BitVec.ofNat 1 0
def internal2_v31103 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := if (internal2_v11528 op valid enable) = (internal2_v24 op valid enable) then 1 else 0
def internal2_v11574 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := BitVec.extractLsb' 5 1 op
def internal2_v11575 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 7 := BitVec.ofNat 7 32
def internal2_v11576 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := if op = (internal2_v11575 op valid enable) then 1 else 0
def internal2_v11577 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := if (internal2_v11576 op valid enable) = (internal2_v24 op valid enable) then 1 else 0
def internal2_v11578 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := ((internal2_v11574 op valid enable) &&& (internal2_v11577 op valid enable))
def internal2_v11579 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 7 := BitVec.ofNat 7 33
def internal2_v11580 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := if op = (internal2_v11579 op valid enable) then 1 else 0
def internal2_v11581 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := if (internal2_v11580 op valid enable) = (internal2_v24 op valid enable) then 1 else 0
def internal2_v11582 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := ((internal2_v11578 op valid enable) &&& (internal2_v11581 op valid enable))
def internal2_v11583 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := (valid &&& (internal2_v11582 op valid enable))
def internal2_v31104 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := if (internal2_v11583 op valid enable) = (internal2_v24 op valid enable) then 1 else 0
def internal2_v31105 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := ((internal2_v31103 op valid enable) ||| (internal2_v31104 op valid enable))
def internal2_v12331 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 7 := BitVec.ofNat 7 32
def internal2_v12332 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := if op = (internal2_v12331 op valid enable) then 1 else 0
def internal2_v12333 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := (valid &&& (internal2_v12332 op valid enable))
def internal2_v31106 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := if (internal2_v12333 op valid enable) = (internal2_v24 op valid enable) then 1 else 0
def internal2_v31107 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := ((internal2_v31105 op valid enable) ||| (internal2_v31106 op valid enable))
def internal2_v11672 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 7 := BitVec.ofNat 7 33
def internal2_v11673 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := if op = (internal2_v11672 op valid enable) then 1 else 0
def internal2_v11674 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := (valid &&& (internal2_v11673 op valid enable))
def internal2_v31108 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := if (internal2_v11674 op valid enable) = (internal2_v24 op valid enable) then 1 else 0
def internal2_v31109 (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : BitVec 1 := ((internal2_v31107 op valid enable) ||| (internal2_v31108 op valid enable))
def internal2_check (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : Prop := enable ≠ 1 ∨ (internal2_v31109 op valid enable) = 1
theorem internal2_tautology (op : BitVec 7) (valid : BitVec 1) (enable : BitVec 1) : internal2_check op valid enable := by
  simp only [internal2_check, internal2_v11527, internal2_v11528, internal2_v24, internal2_v31103, internal2_v11574, internal2_v11575, internal2_v11576, internal2_v11577, internal2_v11578, internal2_v11579, internal2_v11580, internal2_v11581, internal2_v11582, internal2_v11583, internal2_v31104, internal2_v31105, internal2_v12331, internal2_v12332, internal2_v12333, internal2_v31106, internal2_v31107, internal2_v11672, internal2_v11673, internal2_v11674, internal2_v31108, internal2_v31109]
  bv_decide
theorem task_2_always (s : State) (i : Inputs) : TaskHolds 2 s i := by
  change decide ((v31113 s i) ≠ 1 ∨ (v31109 s i) = 1) = true
  apply decide_eq_true
  change internal2_check (v11526 s i) (v11525 s i) (v31113 s i)
  exact internal2_tautology _ _ _
#print axioms task_2_always
def internal11_v24 (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : BitVec 1 := BitVec.ofNat 1 0
def internal11_v31375 (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : BitVec 1 := if reset = (internal11_v24 write dest data commit oldZero reset) then 1 else 0
def internal11_v31376 (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : BitVec 1 := (commit &&& (internal11_v31375 write dest data commit oldZero reset))
def internal11_v11816 (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : BitVec 5 := BitVec.ofNat 5 0
def internal11_v11817 (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : BitVec 1 := if dest ≠ (internal11_v11816 write dest data commit oldZero reset) then 1 else 0
def internal11_v31362 (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : BitVec 5 := BitVec.ofNat 5 0
def internal11_v31363 (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : BitVec 1 := if (internal11_v31362 write dest data commit oldZero reset) = dest then 1 else 0
def internal11_v31364 (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : BitVec 64 := BitVec.ofNat 64 0
def internal11_v31365 (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : BitVec 64 := if (internal11_v31363 write dest data commit oldZero reset) = 1 then data else (internal11_v31364 write dest data commit oldZero reset)
def internal11_v31366 (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : BitVec 64 := BitVec.ofNat 64 0
def internal11_v31367 (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : BitVec 64 := if (internal11_v11817 write dest data commit oldZero reset) = 1 then (internal11_v31365 write dest data commit oldZero reset) else (internal11_v31366 write dest data commit oldZero reset)
def internal11_v31368 (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : BitVec 64 := BitVec.ofNat 64 0
def internal11_v31369 (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : BitVec 64 := if write = 1 then (internal11_v31367 write dest data commit oldZero reset) else (internal11_v31368 write dest data commit oldZero reset)
def internal11_v31370 (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : BitVec 64 := (internal11_v31369 write dest data commit oldZero reset)
def internal11_v31371 (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : BitVec 64 := (internal11_v31370 write dest data commit oldZero reset)
def internal11_v31372 (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : BitVec 64 := (internal11_v31371 write dest data commit oldZero reset)
def internal11_v14559 (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : BitVec 1 := commit
def internal11_v14560 (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : BitVec 1 := (internal11_v14559 write dest data commit oldZero reset)
def internal11_v14561 (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : BitVec 64 := BitVec.ofNat 64 0
def internal11_v14563 (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : BitVec 64 := if (internal11_v14560 write dest data commit oldZero reset) = 1 then (internal11_v14561 write dest data commit oldZero reset) else oldZero
def internal11_v14564 (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : BitVec 64 := (internal11_v14563 write dest data commit oldZero reset)
def internal11_v31373 (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : BitVec 64 := (internal11_v14564 write dest data commit oldZero reset)
def internal11_v31374 (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : BitVec 1 := if (internal11_v31372 write dest data commit oldZero reset) = (internal11_v31373 write dest data commit oldZero reset) then 1 else 0
def internal11_check (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : Prop := (internal11_v31376 write dest data commit oldZero reset) ≠ 1 ∨ (internal11_v31374 write dest data commit oldZero reset) = 1
theorem internal11_tautology (write : BitVec 1) (dest : BitVec 5) (data : BitVec 64) (commit : BitVec 1) (oldZero : BitVec 64) (reset : BitVec 1) : internal11_check write dest data commit oldZero reset := by
  simp only [internal11_check, internal11_v24, internal11_v31375, internal11_v31376, internal11_v11816, internal11_v11817, internal11_v31362, internal11_v31363, internal11_v31364, internal11_v31365, internal11_v31366, internal11_v31367, internal11_v31368, internal11_v31369, internal11_v31370, internal11_v31371, internal11_v31372, internal11_v14559, internal11_v14560, internal11_v14561, internal11_v14563, internal11_v14564, internal11_v31373, internal11_v31374]
  rcases BitVec.eq_zero_or_eq_one commit with h | h <;>
    by_cases hd : dest = 0 <;> simp [h, hd]
  right
  intro _ hn he
  exact False.elim (hn he.symm)
theorem task_11_always (s : State) (i : Inputs) : TaskHolds 11 s i := by
  change decide ((v31376 s i) ≠ 1 ∨ (v31374 s i) = 1) = true
  apply decide_eq_true
  change internal11_check (v11462 s i) (v11465 s i) (v11842 s i) (v14558 s i) (v14562 s i) (v14554 s i)
  exact internal11_tautology _ _ _ _ _ _
#print axioms task_11_always
end NutShellProofs
