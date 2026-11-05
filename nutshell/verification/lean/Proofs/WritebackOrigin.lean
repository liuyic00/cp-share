import Proofs.IssueOperands
namespace NutShellProofs
open nNutCore

private theorem and_ones (a b : BitVec 1) (h : a &&& b = 1) : a = 1 ∧ b = 1 := by
  rcases BitVec.eq_zero_or_eq_one a with ha | ha <;>
    rcases BitVec.eq_zero_or_eq_one b with hb | hb <;> simp_all

theorem next_writeback_origin (s : State) (i next : Inputs)
    (write : v11462 (step s i) next = 1) :
    v6 s i = 1 ∧ v11475 s i = 1 ∧ v11465 (step s i) next = v11470 s i := by
  have both : v11459 (step s i) next = 1 ∧ v9 (step s i) next = 1 := and_ones _ _ write
  have valid := commit_requires_execute_valid s i next both.2
  have cap := capture_decode_ctrl_rfWen s i next both.2
  have enabled : v25485 s i = 1 := cap.symm.trans both.1
  have upper : v25480 s i = 1 := (and_ones _ _ enabled).1
  have wen : v11475 s i = 1 := (and_ones _ _ upper).1
  exact ⟨valid, wen, capture_decode_ctrl_rfDest s i next both.2⟩

theorem alu_next_writeback_enabled (s : State) (i next : Inputs)
    (commit : v9 (step s i) next = 1) (unit : v3 s i = 0) (write : v11475 s i = 1) :
    v11462 (step s i) next = 1 := by
  have notLSU : v11524 s i = 0 := by
    simp [v11524, v11522, v11521, v11520, unit]
  have notCSR : v13180 s i = 0 := by
    simp [v13180, v13178, v13177, v13176, unit]
  have allowed : v25479 s i = 1 := by
    rcases BitVec.eq_zero_or_eq_one (v25477 s i) with h | h <;>
      simp [v25479, v25478, notLSU, v24, h]
  have wen : v11473 s i = 1 := write
  have emitted : v25485 s i = 1 := by
    simp [v25485, v25484, v25480, wen, allowed, v25483, v25482, notCSR, v24]
  have nextWen : v11459 (step s i) next = 1 :=
    (capture_decode_ctrl_rfWen s i next commit).trans emitted
  simp [v11462, v11461, v11460, nextWen, commit]

#print axioms alu_next_writeback_enabled
#print axioms next_writeback_origin
end NutShellProofs
