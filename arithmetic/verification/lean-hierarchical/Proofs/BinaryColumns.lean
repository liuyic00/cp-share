import Std.Tactic

namespace HierarchicalColumns

def weighted : Nat → (Nat → Nat) → Nat
  | 0, _ => 0
  | n + 1, values => values 0 + 2 * weighted n (fun k => values (k + 1))

/-- Adjacent column carries cancel when the column contracts are weighted.
    The terminal carry remains explicit so truncation can be justified. -/
theorem conservation (n : Nat) (inputs outputs carry : Nat → Nat)
    (columns : ∀ k, k < n → inputs k + carry k = outputs k + 2 * carry (k + 1)) :
    weighted n inputs + carry 0 = weighted n outputs + 2^n * carry n := by
  induction n generalizing inputs outputs carry with
  | zero => simp [weighted]
  | succ n ih =>
    have tailBalance := ih (fun k => inputs (k + 1)) (fun k => outputs (k + 1))
      (fun k => carry (k + 1)) (by intro k hk; exact columns (k + 1) (by omega))
    have scaled := congrArg (fun x : Nat => 2 * x) tailBalance
    have headBalance := columns 0 (by omega)
    simp only [Nat.mul_add] at scaled
    simp only [weighted, Nat.pow_succ]
    have rearrange : 2^n * 2 * carry (n + 1) = 2 * (2^n * carry (n + 1)) := by ac_rfl
    rw [rearrange]
    omega

/-- Discarding the terminal carry is sound at the corresponding output width. -/
theorem truncated_conservation (n : Nat) (inputs outputs carry : Nat → Nat)
    (columns : ∀ k, k < n → inputs k + carry k = outputs k + 2 * carry (k + 1))
    (initial : carry 0 = 0) :
    BitVec.ofNat n (weighted n inputs) = BitVec.ofNat n (weighted n outputs) := by
  have balance := conservation n inputs outputs carry columns
  rw [initial, Nat.add_zero] at balance
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  rw [balance]
  simp [Nat.add_mod, Nat.mul_mod]

theorem weighted_congr (n : Nat) (a b : Nat → Nat)
    (same : ∀ k, k < n → a k = b k) : weighted n a = weighted n b := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    simp only [weighted]
    rw [same 0 (by omega), ih (fun k => a (k + 1)) (fun k => b (k + 1))
      (by intro k hk; exact same (k + 1) (by omega))]

def columnAt : List Nat → Nat → Nat
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, k + 1 => columnAt xs k

end HierarchicalColumns
