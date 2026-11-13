import Std.Tactic

/-!
Radix-4 Booth recoding, including the signed top digit correction.
Pairs contain the even and odd bits, least significant pair first.
These arithmetic lemmas do not yet identify the partial rows in the
exported ArrayMulDataModule circuit.
-/
namespace BoothRecoding

abbrev Pair := Bool × Bool

def bit (b : Bool) : Int := if b then 1 else 0

def digit (previous : Bool) (p : Pair) : Int :=
  bit previous + bit p.1 - 2 * bit p.2

def unsigned : List Pair → Int
  | [] => 0
  | p :: ps => bit p.1 + 2 * bit p.2 + 4 * unsigned ps

def top (previous : Bool) : List Pair → Bool
  | [] => previous
  | p :: ps => top p.2 ps

def recoded (previous : Bool) : List Pair → Int
  | [] => 0
  | p :: ps => digit previous p + 4 * recoded p.2 ps

/-- Overlapping Booth windows telescope, retaining the signed top bit. -/
theorem recoded_eq (ps : List Pair) (previous : Bool) :
    recoded previous ps = unsigned ps + bit previous -
      (4 : Int) ^ ps.length * bit (top previous ps) := by
  induction ps generalizing previous with
  | nil => simp [recoded, unsigned, top]
  | cons p ps ih =>
    simp only [recoded, unsigned, top, List.length_cons, ih, digit,
      Int.pow_succ, Int.mul_right_comm]
    omega

/-- The two's-complement interpretation of the paired bits. -/
def signed (ps : List Pair) : Int :=
  unsigned ps - (4 : Int) ^ ps.length * bit (top false ps)

theorem recoded_signed (ps : List Pair) : recoded false ps = signed ps := by
  rw [recoded_eq]
  simp [signed, bit]

def partialProducts (b : Int) (previous : Bool) : List Pair → Int
  | [] => 0
  | p :: ps => digit previous p * b + 4 * partialProducts b p.2 ps

theorem partialProducts_eq (b : Int) (previous : Bool) (ps : List Pair) :
    partialProducts b previous ps = recoded previous ps * b := by
  induction ps generalizing previous with
  | nil => simp [partialProducts, recoded]
  | cons p ps ih =>
    simp only [partialProducts, recoded, ih, Int.add_mul, Int.mul_assoc]

/-- Signed multiplication for arbitrary widths and multiplicands. -/
theorem signed_product (b : Int) (ps : List Pair) :
    partialProducts b false ps = signed ps * b := by
  rw [partialProducts_eq, recoded_signed]

theorem digit_table (previous even odd : Bool) :
    digit previous (even, odd) =
      if odd then (if even then (if previous then 0 else -1)
                   else (if previous then -1 else -2))
      else (if even then (if previous then 2 else 1)
            else (if previous then 1 else 0)) := by
  cases previous <;> cases even <;> cases odd <;> decide

/-- Appending a sign-extension pair preserves the recoded value. -/
theorem sign_extend (ps : List Pair) (previous : Bool) :
    recoded previous (ps ++ [(top previous ps, top previous ps)]) =
      recoded previous ps := by
  induction ps generalizing previous with
  | nil => cases previous <;> decide
  | cons p ps ih =>
    simp only [List.cons_append, recoded, top, ih]

/-- The 66-bit selector used by the 65-bit array multiplier. Negative
rows are stored in ones-complement form; the following row supplies the
correction bits. This theorem accounts for those correction bits locally. -/
def row (b : BitVec 66) (window : BitVec 3) : BitVec 66 :=
  if window == 1 || window == 2 then b
  else if window == 3 then b <<< 1
  else if window == 4 then (~~~b) <<< 1
  else if window == 5 || window == 6 then ~~~b
  else 0

def correction (window : BitVec 3) : BitVec 66 :=
  if window == 4 then 2 else if window == 5 || window == 6 then 1 else 0

theorem corrected_row (b : BitVec 66) (window : BitVec 3) :
    row b window + correction window =
      (if window == 1 || window == 2 then b
       else if window == 3 then b <<< 1
       else if window == 4 then -(b <<< 1)
       else if window == 5 || window == 6 then -b
       else 0) := by
  simp only [row, correction]
  bv_decide

/-- Connect the concrete selector and its correction to the integer digit
used in the unbounded signed-product theorem. -/
theorem corrected_row_digit (b : BitVec 66) (previous even odd : Bool) :
    let window := BitVec.ofBool odd ++ BitVec.ofBool even ++ BitVec.ofBool previous
    row b window + correction window =
      b * BitVec.ofInt 66 (digit previous (even, odd)) := by
  dsimp only
  rw [corrected_row]
  cases previous <;> cases even <;> cases odd <;>
    simp [digit, bit]
  · change -b <<< 1 = b * -(2#66)
    rw [BitVec.mul_neg, BitVec.mul_two]
    bv_decide
  · change -b = b * -(1#66)
    rw [BitVec.mul_neg, BitVec.mul_one]
  · change -b = b * -(1#66)
    rw [BitVec.mul_neg, BitVec.mul_one]
  · rw [BitVec.mul_two]
    bv_decide

end BoothRecoding
