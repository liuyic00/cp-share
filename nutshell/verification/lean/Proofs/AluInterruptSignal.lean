import Proofs.AluInterrupts
namespace NutShellProofs
open nNutCore

theorem alu_interrupt_signal_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    v13720 (run initial inputs (t + 1)) (inputs (t + 1)) = 0 := by
  have clear := (alu_interrupt_run initial inputs reset t).2 valid unit
  rcases clear with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩
  simp [v13685, v13686, v13687, v13688, v13689, v13690, v13691, v13692, v13693, v13694, v13695, v13696, v13697, v13698, v13699, v13700, v13701, v13702, v13703, v13704, v13705, v13706, v13707, v13708, v13709, v13710, v13711, v13712, v13713, v13714, v13715, v13716, v13717, v13718, v13719, v13720, v10038, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11]

theorem alu_trap_is_exception_run (initial : State) (inputs : Nat → Inputs)
    (reset : (inputs 0).g0.nreset = 1) (t : Nat)
    (valid : v6 (run initial inputs (t + 1)) (inputs (t + 1)) = 1)
    (unit : v3 (run initial inputs (t + 1)) (inputs (t + 1)) = 0) :
    v13725 (run initial inputs (t + 1)) (inputs (t + 1)) =
      v13684 (run initial inputs (t + 1)) (inputs (t + 1)) &&&
      v13724 (run initial inputs (t + 1)) (inputs (t + 1)) := by
  rcases BitVec.eq_zero_or_eq_one
    (v13684 (run initial inputs (t + 1)) (inputs (t + 1))) with h | h <;>
    simp [v13725, v13721, alu_interrupt_signal_run initial inputs reset t valid unit, h]

#print axioms alu_interrupt_signal_run
#print axioms alu_trap_is_exception_run
end NutShellProofs
