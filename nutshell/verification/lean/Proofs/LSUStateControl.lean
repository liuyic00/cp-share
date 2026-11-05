import Proofs.BranchNoTrap
namespace NutShellProofs
open nNutCore

theorem lsu_idle_reset (s : State) (i : Inputs) (reset : i.g0.nreset = 1) :
    (step s i).g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0 := by
  change v12355 s i = 0
  simp [v12355, v12234, v12103, v11455, reset, v2687]

theorem lsu_idle_without_request (s : State) (i : Inputs)
    (idle : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0)
    (inactive : v11525 s i = 0) :
    (step s i).g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0 := by
  change v12355 s i = 0
  simp [v12355, v12354, v12353, v11519, idle, v2687, v12336,
    v11674, inactive, v12335, v12333, v12334, v11583]

theorem busy_lsu_completion_returns_idle (s : State) (i : Inputs)
    (busy : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate ≠ 0)
    (complete : v11698 s i = 1) :
    (step s i).g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0 := by
  have bound := s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate.isLt
  have cases : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate.toNat = 0 ∨ s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate.toNat = 1 ∨ s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate.toNat = 2 ∨ s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate.toNat = 3 ∨ s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate.toNat = 4 ∨ s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate.toNat = 5 ∨ s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate.toNat = 6 ∨ s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate.toNat = 7 := by omega
  rcases cases with h | h | h | h | h | h | h | h
  · have eq : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = (0 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
    change v12355 s i = 0
    rcases BitVec.eq_zero_or_eq_one (v11639 s i) with fault | fault <;>
      rcases BitVec.eq_zero_or_eq_one (v11667 s i) with response | response <;>
      simp [v12337, v12338, v12339, v12340, v12341, v12342, v12343, v12344, v12345, v12346, v12347, v12348, v12349, v12350, v12351, v12352, v12353, v12354, v12355, v11677, v11678, v11679, v11680, v11681, v11682, v11683, v11684, v11685, v11686, v11687, v11688, v11689, v11690, v11691, v11692, v11693, v11694, v11695, v11696, v11697, v11698, v11531, v11532, v11533, v11534, v11535, v11536, v11537, v11538, v11539, v11519, v2687, v4, v97, v9701, v24, v110, v12234, v12103, v11455, eq, fault, response] at busy complete ⊢
  · have eq : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = (1 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
    change v12355 s i = 0
    rcases BitVec.eq_zero_or_eq_one (v11639 s i) with fault | fault <;>
      rcases BitVec.eq_zero_or_eq_one (v11667 s i) with response | response <;>
      simp [v12337, v12338, v12339, v12340, v12341, v12342, v12343, v12344, v12345, v12346, v12347, v12348, v12349, v12350, v12351, v12352, v12353, v12354, v12355, v11677, v11678, v11679, v11680, v11681, v11682, v11683, v11684, v11685, v11686, v11687, v11688, v11689, v11690, v11691, v11692, v11693, v11694, v11695, v11696, v11697, v11698, v11531, v11532, v11533, v11534, v11535, v11536, v11537, v11538, v11539, v11519, v2687, v4, v97, v9701, v24, v110, v12234, v12103, v11455, eq, fault, response] at busy complete ⊢
  · have eq : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = (2 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
    change v12355 s i = 0
    rcases BitVec.eq_zero_or_eq_one (v11639 s i) with fault | fault <;>
      rcases BitVec.eq_zero_or_eq_one (v11667 s i) with response | response <;>
      simp [v12337, v12338, v12339, v12340, v12341, v12342, v12343, v12344, v12345, v12346, v12347, v12348, v12349, v12350, v12351, v12352, v12353, v12354, v12355, v11677, v11678, v11679, v11680, v11681, v11682, v11683, v11684, v11685, v11686, v11687, v11688, v11689, v11690, v11691, v11692, v11693, v11694, v11695, v11696, v11697, v11698, v11531, v11532, v11533, v11534, v11535, v11536, v11537, v11538, v11539, v11519, v2687, v4, v97, v9701, v24, v110, v12234, v12103, v11455, eq, fault, response] at busy complete ⊢
  · have eq : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = (3 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
    change v12355 s i = 0
    rcases BitVec.eq_zero_or_eq_one (v11639 s i) with fault | fault <;>
      rcases BitVec.eq_zero_or_eq_one (v11667 s i) with response | response <;>
      simp [v12337, v12338, v12339, v12340, v12341, v12342, v12343, v12344, v12345, v12346, v12347, v12348, v12349, v12350, v12351, v12352, v12353, v12354, v12355, v11677, v11678, v11679, v11680, v11681, v11682, v11683, v11684, v11685, v11686, v11687, v11688, v11689, v11690, v11691, v11692, v11693, v11694, v11695, v11696, v11697, v11698, v11531, v11532, v11533, v11534, v11535, v11536, v11537, v11538, v11539, v11519, v2687, v4, v97, v9701, v24, v110, v12234, v12103, v11455, eq, fault, response] at busy complete ⊢
  · have eq : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = (4 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
    change v12355 s i = 0
    rcases BitVec.eq_zero_or_eq_one (v11639 s i) with fault | fault <;>
      rcases BitVec.eq_zero_or_eq_one (v11667 s i) with response | response <;>
      simp [v12337, v12338, v12339, v12340, v12341, v12342, v12343, v12344, v12345, v12346, v12347, v12348, v12349, v12350, v12351, v12352, v12353, v12354, v12355, v11677, v11678, v11679, v11680, v11681, v11682, v11683, v11684, v11685, v11686, v11687, v11688, v11689, v11690, v11691, v11692, v11693, v11694, v11695, v11696, v11697, v11698, v11531, v11532, v11533, v11534, v11535, v11536, v11537, v11538, v11539, v11519, v2687, v4, v97, v9701, v24, v110, v12234, v12103, v11455, eq, fault, response] at busy complete ⊢
  · have eq : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = (5 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
    change v12355 s i = 0
    rcases BitVec.eq_zero_or_eq_one (v11639 s i) with fault | fault <;>
      rcases BitVec.eq_zero_or_eq_one (v11667 s i) with response | response <;>
      simp [v12337, v12338, v12339, v12340, v12341, v12342, v12343, v12344, v12345, v12346, v12347, v12348, v12349, v12350, v12351, v12352, v12353, v12354, v12355, v11677, v11678, v11679, v11680, v11681, v11682, v11683, v11684, v11685, v11686, v11687, v11688, v11689, v11690, v11691, v11692, v11693, v11694, v11695, v11696, v11697, v11698, v11531, v11532, v11533, v11534, v11535, v11536, v11537, v11538, v11539, v11519, v2687, v4, v97, v9701, v24, v110, v12234, v12103, v11455, eq, fault, response] at busy complete ⊢
  · have eq : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = (6 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
    change v12355 s i = 0
    rcases BitVec.eq_zero_or_eq_one (v11639 s i) with fault | fault <;>
      rcases BitVec.eq_zero_or_eq_one (v11667 s i) with response | response <;>
      simp [v12337, v12338, v12339, v12340, v12341, v12342, v12343, v12344, v12345, v12346, v12347, v12348, v12349, v12350, v12351, v12352, v12353, v12354, v12355, v11677, v11678, v11679, v11680, v11681, v11682, v11683, v11684, v11685, v11686, v11687, v11688, v11689, v11690, v11691, v11692, v11693, v11694, v11695, v11696, v11697, v11698, v11531, v11532, v11533, v11534, v11535, v11536, v11537, v11538, v11539, v11519, v2687, v4, v97, v9701, v24, v110, v12234, v12103, v11455, eq, fault, response] at busy complete ⊢
  · have eq : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = (7 : BitVec 3) := BitVec.eq_of_toNat_eq (by simpa using h)
    change v12355 s i = 0
    rcases BitVec.eq_zero_or_eq_one (v11639 s i) with fault | fault <;>
      rcases BitVec.eq_zero_or_eq_one (v11667 s i) with response | response <;>
      simp [v12337, v12338, v12339, v12340, v12341, v12342, v12343, v12344, v12345, v12346, v12347, v12348, v12349, v12350, v12351, v12352, v12353, v12354, v12355, v11677, v11678, v11679, v11680, v11681, v11682, v11683, v11684, v11685, v11686, v11687, v11688, v11689, v11690, v11691, v11692, v11693, v11694, v11695, v11696, v11697, v11698, v11531, v11532, v11533, v11534, v11535, v11536, v11537, v11538, v11539, v11519, v2687, v4, v97, v9701, v24, v110, v12234, v12103, v11455, eq, fault, response] at busy complete ⊢


theorem alu_idle_lsu_step (s : State) (i : Inputs)
    (unit : v3 s i = 0)
    (idle : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0) :
    (step s i).g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0 := by
  apply lsu_idle_without_request s i idle
  simp [v11525, v11524, v11522, v11521, v11520, unit]

theorem lsu_capture_requires_completion (s : State) (i : Inputs)
    (unit : v3 s i = 1) (valid : v6 s i = 1) (capture : v24283 s i = 1) :
    v11698 s i = 1 := by
  rcases BitVec.eq_zero_or_eq_one (v11698 s i) with zero | one
  · simp [v24283, v11705, v11704, v11491, v24, valid, v11703,
      v11702, v11701, v11700, v11495, v11494, unit, v11699,
      v11518, v11517, zero] at capture
  · exact one

theorem busy_lsu_capture_returns_idle (s : State) (i : Inputs)
    (unit : v3 s i = 1) (valid : v6 s i = 1) (capture : v24283 s i = 1)
    (busy : s.g41.r1343_nbackend_5Fexu_5Flsu_5Fstate ≠ 0) :
    (step s i).g41.r1343_nbackend_5Fexu_5Flsu_5Fstate = 0 := by
  exact busy_lsu_completion_returns_idle s i busy
    (lsu_capture_requires_completion s i unit valid capture)

#print axioms alu_idle_lsu_step
#print axioms lsu_capture_requires_completion
#print axioms busy_lsu_capture_returns_idle
#print axioms lsu_idle_reset
#print axioms lsu_idle_without_request
#print axioms busy_lsu_completion_returns_idle
end NutShellProofs
