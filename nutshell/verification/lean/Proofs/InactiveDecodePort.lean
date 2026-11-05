import Proofs.IDUHandshake
namespace NutShellProofs
open nNutCore

/-- The second frontend decode port is disabled in this exported configuration. -/
theorem idu_second_port_disabled (s : State) (i : Inputs) : v26193 s i = 0 := by
  rfl

/-- Two-instruction enqueue is impossible, independent of arbitrary invalid-port inputs. -/
theorem idu_two_instruction_enqueue_disabled (s : State) (i : Inputs) : v26202 s i = 0 := by
  rcases BitVec.eq_zero_or_eq_one (v9827 s i) with zero | one <;>
    simp [v26202, v26201, v26199, v26200, idu_second_port_disabled, v24, v9721, *]

/-- Whenever the single-instruction path is selected, it selects the active port. -/
theorem idu_single_enqueue_active_port (s : State) (i : Inputs)
    (enqueue : v26215 s i = 1) : v9827 s i = 1 := by
  rcases BitVec.eq_zero_or_eq_one (v9827 s i) with zero | one
  · simp [v26215, v26214, v26201, v26199, v26200,
      idu_second_port_disabled, v24, zero] at enqueue
  · exact one
#print axioms idu_two_instruction_enqueue_disabled
#print axioms idu_single_enqueue_active_port
end NutShellProofs
