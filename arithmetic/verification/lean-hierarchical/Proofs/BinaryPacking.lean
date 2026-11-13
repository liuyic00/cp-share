import Proofs.BinaryColumns

namespace HierarchicalColumns

def pack : (n : Nat) → (Nat → BitVec 1) → BitVec n
  | 0, _ => 0
  | n + 1, bits => pack n (fun k => bits (k + 1)) ++ bits 0

theorem pack_toNat (n : Nat) (bits : Nat → BitVec 1) :
    (pack n bits).toNat = weighted n (fun k => (bits k).toNat) := by
  induction n generalizing bits with
  | zero => rfl
  | succ n ih =>
    simp only [pack, BitVec.toNat_append, ih]
    rw [← Nat.shiftLeft_add_eq_or_of_lt (bits 0).isLt]
    simp only [weighted, Nat.shiftLeft_eq, Nat.pow_one]
    omega

theorem weighted_add (n : Nat) (a b : Nat → Nat) :
    weighted n (fun k => a k + b k) = weighted n a + weighted n b := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    simp only [weighted, ih, Nat.mul_add]
    omega

theorem pack_eq_weighted (n : Nat) (bits : Nat → BitVec 1) :
    pack n bits = BitVec.ofNat n (weighted n (fun k => (bits k).toNat)) := by
  rw [← pack_toNat]
  simpa using (BitVec.ofNat_toNat n (pack n bits)).symm

def bitAt : List (BitVec 1) → Nat → BitVec 1
  | [], _ => 0
  | x :: _, 0 => x
  | _ :: xs, k + 1 => bitAt xs k

def packList : (bits : List (BitVec 1)) → BitVec bits.length
  | [] => 0
  | x :: xs => packList xs ++ x

theorem pack_list (bits : List (BitVec 1)) :
    pack bits.length (bitAt bits) = packList bits := by
  induction bits with
  | nil => rfl
  | cons x xs ih =>
    change pack xs.length (bitAt xs) ++ x = packList xs ++ x
    rw [ih]

end HierarchicalColumns
