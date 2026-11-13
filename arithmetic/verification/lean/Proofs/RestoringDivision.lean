import Std

/- Arithmetic lemmas for the restoring-division datapath. All variables are
   unbounded naturals; there is no bounded enumeration of input operands. -/
namespace RestoringDivision

def digit (candidate divisor : Nat) : Nat := if divisor ≤ candidate then 1 else 0

def restore (candidate divisor : Nat) : Nat :=
  if divisor ≤ candidate then candidate - divisor else candidate

/-- One subtraction suffices when the incoming candidate is below twice the
    positive divisor, and precisely accounts for the next quotient bit. -/
theorem restore_correct (candidate divisor : Nat)
    (_positive : 0 < divisor) (bound : candidate < 2 * divisor) :
    candidate = digit candidate divisor * divisor + restore candidate divisor ∧
    restore candidate divisor < divisor ∧ digit candidate divisor ≤ 1 := by
  unfold digit restore
  split <;> simp_all <;> omega

structure Accumulator where
  quotient : Nat
  remainder : Nat
  deriving Repr, DecidableEq

def step (s : Accumulator) (divisor bit : Nat) : Accumulator :=
  let candidate := 2 * s.remainder + bit
  { quotient := 2 * s.quotient + digit candidate divisor,
    remainder := restore candidate divisor }

/-- Processing one binary digit preserves the full integer division identity
    and the strict remainder bound. -/
theorem step_correct (s : Accumulator) (consumed divisor bit : Nat)
    (positive : 0 < divisor) (binary : bit ≤ 1)
    (identity : consumed = s.quotient * divisor + s.remainder)
    (bound : s.remainder < divisor) :
    2 * consumed + bit = (step s divisor bit).quotient * divisor +
      (step s divisor bit).remainder ∧
    (step s divisor bit).remainder < divisor := by
  have h := restore_correct (2 * s.remainder + bit) divisor positive (by omega)
  dsimp [step]
  constructor
  · rw [identity]
    simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
    omega
  · exact h.2.1

def value : List Nat → Nat → Nat
  | [], consumed => consumed
  | bit :: bits, consumed => value bits (2 * consumed + bit)

def run : List Nat → Accumulator → Nat → Accumulator
  | [], s, _ => s
  | bit :: bits, s, divisor => run bits (step s divisor bit) divisor

/-- Restoring division over any finite sequence of binary digits. -/
theorem run_correct (bits : List Nat) (s : Accumulator) (consumed divisor : Nat)
    (positive : 0 < divisor) (binary : ∀ bit ∈ bits, bit ≤ 1)
    (identity : consumed = s.quotient * divisor + s.remainder)
    (bound : s.remainder < divisor) :
    value bits consumed = (run bits s divisor).quotient * divisor +
      (run bits s divisor).remainder ∧
    (run bits s divisor).remainder < divisor := by
  induction bits generalizing s consumed with
  | nil => exact ⟨identity, bound⟩
  | cons bit bits ih =>
      have h := step_correct s consumed divisor bit positive (binary bit (by simp)) identity bound
      exact ih (step s divisor bit) (2 * consumed + bit)
        (by intro b hb; exact binary b (by simp [hb])) h.1 h.2

/-- The invariant determines the ordinary quotient and remainder uniquely. -/
theorem quotient_remainder (s : Accumulator) (consumed divisor : Nat)
    (positive : 0 < divisor)
    (identity : consumed = s.quotient * divisor + s.remainder)
    (bound : s.remainder < divisor) :
    s.quotient = consumed / divisor ∧ s.remainder = consumed % divisor := by
  rw [identity]
  constructor
  · rw [Nat.add_comm, Nat.add_mul_div_right _ _ positive, Nat.div_eq_of_lt bound]
    simp
  · simp [Nat.add_mod, Nat.mod_eq_of_lt bound]

/-- Starting from zero computes natural division of the entire bit sequence. -/
theorem divides (bits : List Nat) (divisor : Nat)
    (positive : 0 < divisor) (binary : ∀ bit ∈ bits, bit ≤ 1) :
    let result := run bits ⟨0, 0⟩ divisor
    result.quotient = value bits 0 / divisor ∧
      result.remainder = value bits 0 % divisor := by
  have h := run_correct bits ⟨0, 0⟩ 0 divisor positive binary (by simp) positive
  exact quotient_remainder _ _ _ positive h.1 h.2
end RestoringDivision
