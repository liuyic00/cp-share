import Std.Tactic

namespace HierarchicalBooth

/-- Radix-four positional value, least significant digit first. -/
def weighted : Nat → (Nat → Int) → Int
  | 0, _ => 0
  | n + 1, digits => digits 0 + 4 * weighted n (fun k => digits (k + 1))

/-- The overlap bit carried between Booth groups telescopes. This identity
    separates local recoding from the width-dependent final sign correction. -/
theorem recoding_balance (n : Nat) (digits chunks carry : Nat → Int)
    (localBalance : ∀ k, k < n → digits k + 4 * carry (k + 1) = chunks k + carry k) :
    weighted n digits + (4 : Int) ^ n * carry n = weighted n chunks + carry 0 := by
  induction n generalizing digits chunks carry with
  | zero => simp [weighted]
  | succ n ih =>
    have tailBalance := ih (fun k => digits (k + 1)) (fun k => chunks (k + 1))
      (fun k => carry (k + 1)) (by intro k hk; exact localBalance (k + 1) (by omega))
    have scaled := congrArg (fun x : Int => 4 * x) tailBalance
    have headBalance := localBalance 0 (by omega)
    simp only [weighted, Int.pow_succ]
    simp only [Int.mul_add] at scaled
    have commute : (4 : Int) ^ n * 4 * carry (n + 1) =
        4 * ((4 : Int) ^ n * carry (n + 1)) := by
      simp only [Int.mul_assoc, Int.mul_comm]
    rw [commute]
    omega

/-- Each two-bit chunk is recoded using its incoming overlap bit. -/
theorem digit_balance (chunk carry : Int) :
    (chunk % 2 - 2 * (chunk / 2) + carry) + 4 * (chunk / 2) = chunk + carry := by
  omega

/-- A complete finite Booth expansion, including its terminal sign correction. -/
theorem recoding_value (n : Nat) (chunks carry : Nat → Int)
    (overlap : ∀ k, k < n → carry (k + 1) = chunks k / 2) :
    weighted n (fun k => chunks k % 2 - 2 * (chunks k / 2) + carry k) =
      weighted n chunks + carry 0 - (4 : Int) ^ n * carry n := by
  have balance := recoding_balance n
    (fun k => chunks k % 2 - 2 * (chunks k / 2) + carry k) chunks carry
    (by intro k hk; rw [overlap k hk]; exact digit_balance _ _)
  omega

private theorem weighted_zero (n : Nat) : weighted n (fun _ => 0) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [weighted, ih, Int.mul_zero, Int.add_zero]

/-- Positional decomposition telescopes even for signed integer quotients. -/
theorem chunk_value (n : Nat) (chunks quotient : Nat → Int)
    (division : ∀ k, k < n → chunks k + 4 * quotient (k + 1) = quotient k) :
    weighted n chunks + (4 : Int) ^ n * quotient n = quotient 0 := by
  have result := recoding_balance n chunks (fun _ => 0) quotient
    (by intro k hk; simpa only [Int.zero_add] using division k hk)
  simpa only [weighted_zero, Int.zero_add] using result

/-- Sign extension cancels the terminal quotient against the last overlap bit. -/
theorem signed_recoding (n : Nat) (chunks quotient carry : Nat → Int)
    (division : ∀ k, k < n → chunks k + 4 * quotient (k + 1) = quotient k)
    (overlap : ∀ k, k < n → carry (k + 1) = chunks k / 2)
    (initial : carry 0 = 0) (terminal : quotient n + carry n = 0) :
    weighted n (fun k => chunks k % 2 - 2 * (chunks k / 2) + carry k) = quotient 0 := by
  have chunksValue := chunk_value n chunks quotient division
  have recoded := recoding_value n chunks carry overlap
  have cancellation := congrArg (fun x : Int => (4 : Int) ^ n * x) terminal
  simp only [Int.mul_add, Int.mul_zero] at cancellation
  rw [initial] at recoded
  omega

theorem weighted_product (n : Nat) (digits : Nat → Int) (b : Int) :
    weighted n (fun k => digits k * b) = weighted n digits * b := by
  induction n generalizing digits with
  | zero => simp [weighted]
  | succ n ih => simp only [weighted, ih, Int.add_mul, Int.mul_assoc]

/-- Weighted Booth partial products sum to the signed operand product. -/
theorem signed_product (n : Nat) (chunks quotient carry : Nat → Int) (b : Int)
    (division : ∀ k, k < n → chunks k + 4 * quotient (k + 1) = quotient k)
    (overlap : ∀ k, k < n → carry (k + 1) = chunks k / 2)
    (initial : carry 0 = 0) (terminal : quotient n + carry n = 0) :
    weighted n (fun k => (chunks k % 2 - 2 * (chunks k / 2) + carry k) * b) =
      quotient 0 * b := by
  rw [weighted_product, signed_recoding n chunks quotient carry division overlap initial terminal]

end HierarchicalBooth
