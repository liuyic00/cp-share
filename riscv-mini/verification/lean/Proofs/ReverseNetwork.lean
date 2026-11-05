import Proofs.AluCone
set_option linter.unusedSimpArgs false
namespace RiscvMiniProofs
theorem input_reverse_network (op : BitVec 4) (a b : BitVec 32) :
    alu_v8104 op a b = a.reverse := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15 ∨ j = 16 ∨ j = 17 ∨ j = 18 ∨ j = 19 ∨ j = 20 ∨ j = 21 ∨ j = 22 ∨ j = 23 ∨ j = 24 ∨ j = 25 ∨ j = 26 ∨ j = 27 ∨ j = 28 ∨ j = 29 ∨ j = 30 ∨ j = 31 := by omega
  rcases cases with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  all_goals subst j
  all_goals simp [alu_v2012, alu_v2100, alu_v32, alu_v4, alu_v725, alu_v8060, alu_v8061, alu_v8062, alu_v8063, alu_v8064, alu_v8065, alu_v8066, alu_v8067, alu_v8068, alu_v8069, alu_v8070, alu_v8071, alu_v8072, alu_v8073, alu_v8074, alu_v8075, alu_v8076, alu_v8077, alu_v8078, alu_v8079, alu_v8080, alu_v8081, alu_v8082, alu_v8083, alu_v8084, alu_v8085, alu_v8086, alu_v8087, alu_v8088, alu_v8089, alu_v8090, alu_v8091, alu_v8092, alu_v8093, alu_v8094, alu_v8095, alu_v8096, alu_v8097, alu_v8098, alu_v8099, alu_v8100, alu_v8101, alu_v8102, alu_v8103, alu_v8104, BitVec.getElem_append (n := 1) (m := 31), BitVec.getElem_append (n := 2) (m := 30), BitVec.getElem_append (n := 4) (m := 28), BitVec.getElem_append (n := 8) (m := 24), BitVec.getElem_append (n := 16) (m := 16), BitVec.getElem_append (n := 24) (m := 8), BitVec.getElem_append (n := 28) (m := 4), BitVec.getElem_append (n := 30) (m := 2), BitVec.getElem_append (n := 31) (m := 1), BitVec.getElem_reverse (w := 32), BitVec.getMsbD_eq_getLsbD]

theorem output_reverse_network (op : BitVec 4) (a b : BitVec 32) :
    alu_v8148 op a b = (alu_v8112 op a b).reverse := by
  change alu_v8104 op (alu_v8112 op a b) b = _
  exact input_reverse_network _ _ _
#print axioms input_reverse_network
end RiscvMiniProofs
