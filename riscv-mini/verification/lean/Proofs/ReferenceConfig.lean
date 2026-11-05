import Proofs.Contract
namespace RiscvMiniProofs
open nCoreSoc

-- Fixed configuration proved from the original generated state transitions.
structure ReferenceConfig (s : State) : Prop where
  misa : s.g2.r86_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fprivilege_5Fcsr_5Fmisa = 1073746176
  mxlen : s.g3.r119_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fprivilege_5Fcsr_5FMXLEN = 32
  ialign : s.g3.r120_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fprivilege_5Fcsr_5FIALIGN = 32
  ilen : s.g3.r121_ndut_5Fdpath_5Fchecker_5FspecCore_5Fstate_5Fprivilege_5Fcsr_5FILEN = 32

theorem reference_config_reset (s : State) (i : Inputs) (reset : i.nreset = 1) :
    ReferenceConfig (step s i) := by
  constructor
  · change v6939 s i = 1073746176
    simp [v6939, v6938, v6937, v2194, v956, v955, v1, v0, reset]
  · change v7284 s i = 32
    simp [v7284, v7283, v6796, v6795, v956, v955, v1, v0, reset]
  · change v7287 s i = 32
    simp [v7287, v7286, v7285, v6795, v956, v955, v1, v0, reset]
  · change v7290 s i = 32
    simp [v7290, v7289, v7288, v6795, v956, v955, v1, v0, reset]

theorem reference_config_step (s : State) (i : Inputs) (config : ReferenceConfig s) :
    ReferenceConfig (step s i) := by
  constructor
  · change v6939 s i = 1073746176
    simp [v6939, v6938, v6937, v2194, config.misa]
  · change v7284 s i = 32
    simp [v7284, v7283, v6796, v6795, config.mxlen]
  · change v7287 s i = 32
    simp [v7287, v7286, v7285, v6795, config.ialign]
  · change v7290 s i = 32
    simp [v7290, v7289, v7288, v6795, config.ilen]

theorem reference_config_reachable (initial : State) (inputs : Nat → Inputs)
    (cycles : Nat) (reset : ResetPrefix inputs cycles) (t : Nat) (ht : cycles ≤ t) :
    ReferenceConfig (run initial inputs t) := by
  induction t with
  | zero => have := reset.1; omega
  | succ n ih =>
    change ReferenceConfig (step (run initial inputs n) (inputs n))
    by_cases hn : cycles ≤ n
    · exact reference_config_step _ _ (ih hn)
    · exact reference_config_reset _ _ (reset.2.1 n (by omega))

#print axioms reference_config_reachable
end RiscvMiniProofs
