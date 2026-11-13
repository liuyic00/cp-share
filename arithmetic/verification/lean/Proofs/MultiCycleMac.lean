import Generated.MultiCycleMac

namespace nMultiCycleMac
/-- Full-width unsigned arithmetic specification. -/
def arithmetic (a b c : BitVec 8) : BitVec 17 :=
  (0#8 ++ ((0#1 ++ a) + (0#1 ++ b))) * (0#9 ++ c)

/-- Two edges after the accepting edge, valid is high and the result uses the
    accepted inputs. Later input values and downstream readiness are arbitrary. -/
theorem completes_after_two (s : State) (accept add multiply output : Inputs)
    (idle : s.r0_nstate = 0)
    (r0 : accept.nreset = 0) (valid : accept.nio_5Fin_5Fvalid = 1)
    (r1 : add.nreset = 0) (r2 : multiply.nreset = 0) (r3 : output.nreset = 0) :
    let final := observe (step (step (step s accept) add) multiply) output
    final.nio_5Fout_5Fvalid = 1 ∧
    final.nio_5Fout_5Fbits = arithmetic accept.nio_5Fin_5Fbits_5Fa
      accept.nio_5Fin_5Fbits_5Fb accept.nio_5Fin_5Fbits_5Fc := by
  simp [observe, step, eval, arithmetic, idle, r0, valid, r1, r2, r3]

/-- No early completion at either intermediate stage. -/
theorem no_early_output (s : State) (accept add multiply : Inputs)
    (idle : s.r0_nstate = 0)
    (r0 : accept.nreset = 0) (valid : accept.nio_5Fin_5Fvalid = 1)
    (r1 : add.nreset = 0) (r2 : multiply.nreset = 0) :
    (observe (step s accept) add).nio_5Fout_5Fvalid = 0 ∧
    (observe (step (step s accept) add) multiply).nio_5Fout_5Fvalid = 0 := by
  simp [observe, step, eval, idle, r0, valid, r1, r2]

/-- A reset edge establishes idle regardless of uninitialized data registers. -/
theorem reset_idle (s : State) (i : Inputs) (reset : i.nreset = 1) :
    (step s i).r0_nstate = 0 := by
  simp [step, eval, reset]

/-- Backpressure retains the output without restrictions on new input pins. -/
theorem stall_stable (s : State) (i j : Inputs)
    (state : s.r0_nstate = 3) (reset : i.nreset = 0)
    (ready : i.nio_5Fout_5Fready = 0) (nextReset : j.nreset = 0) :
    (observe (step s i) j).nio_5Fout_5Fvalid = 1 ∧
    (observe (step s i) j).nio_5Fout_5Fbits = (observe s i).nio_5Fout_5Fbits := by
  simp [observe, step, eval, state, reset, ready, nextReset]
/-- The bit-vector specification is also the mathematical natural-number result:
    neither the widened addition nor the multiplication overflows. -/
theorem arithmetic_toNat (a b c : BitVec 8) :
    (arithmetic a b c).toNat = (a.toNat + b.toNat) * c.toNat := by
  have ha := a.isLt
  have hb := b.isLt
  have hc := c.isLt
  have hs : a.toNat + b.toNat < 512 := by omega
  have hp : (a.toNat + b.toNat) * c.toNat < 131072 := by
    have h := Nat.mul_le_mul (show a.toNat + b.toNat ≤ 510 by omega)
      (show c.toNat ≤ 255 by omega)
    omega
  unfold arithmetic
  rw [BitVec.toNat_mul, BitVec.toNat_append, BitVec.toNat_append,
    BitVec.toNat_add, BitVec.toNat_append, BitVec.toNat_append]
  simp [Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hp]
/-- Inductive stage and history invariants, including all assertion monitors. -/
def Invariant (s : State) : Prop :=
  ((s.r0_nstate = 2 ∨ s.r0_nstate = 3) →
    s.r4_nsum = (0#1 ++ s.r1_noperands_5Fa) + (0#1 ++ s.r2_noperands_5Fb)) ∧
  (s.r0_nstate = 3 → s.r5_nresult =
    arithmetic s.r1_noperands_5Fa s.r2_noperands_5Fb s.r3_noperands_5Fc) ∧
  (s.r6_naccepted = 1 → s.r0_nstate = 1) ∧
  (s.r7_nwasAdding = 1 → s.r0_nstate = 2) ∧
  (s.r8_nwasMultiplying = 1 → s.r0_nstate = 3) ∧
  (s.r9_nstalled = 1 → s.r0_nstate = 3 ∧ s.r10_npreviousOutput = s.r5_nresult)

theorem reset_invariant (s : State) (i : Inputs) (reset : i.nreset = 1) :
    Invariant (step s i) := by
  simp [Invariant, step, eval, reset]

set_option maxHeartbeats 2000000 in
theorem invariant_step (s : State) (i : Inputs) (h : Invariant s) :
    Invariant (step s i) := by
  have hs : s.r0_nstate = 0 ∨ s.r0_nstate = 1 ∨ s.r0_nstate = 2 ∨ s.r0_nstate = 3 := by bv_decide
  have hr : i.nreset = 0 ∨ i.nreset = 1 := by bv_decide
  have hv : i.nio_5Fin_5Fvalid = 0 ∨ i.nio_5Fin_5Fvalid = 1 := by bv_decide
  have hd : i.nio_5Fout_5Fready = 0 ∨ i.nio_5Fout_5Fready = 1 := by bv_decide
  rcases hs with hs | hs | hs | hs <;>
    rcases hr with hr | hr <;> rcases hv with hv | hv <;> rcases hd with hd | hd <;>
    simp_all [Invariant, arithmetic, step, eval]

set_option maxHeartbeats 2000000 in
theorem invariant_asserts (s : State) (i : Inputs) (h : Invariant s) : asserts s i := by
  simp only [Invariant, arithmetic, asserts, eval, List.all_cons, List.all_nil,
    Bool.and_true, id_eq, Bool.and_eq_true, decide_eq_true_eq] at *
  bv_decide

/-- All exported Chisel assertions hold on every cycle following a reset edge,
    for arbitrary subsequent inputs, including further resets. -/
theorem assertions_after_reset (s : State) (resetInput : Inputs)
    (reset : resetInput.nreset = 1) (inputs : Nat → Inputs) (n : Nat) :
    asserts (run (step s resetInput) inputs n) (inputs n) := by
  apply invariant_asserts
  induction n with
  | zero => exact reset_invariant s resetInput reset
  | succ n ih => exact invariant_step _ _ ih
end nMultiCycleMac
