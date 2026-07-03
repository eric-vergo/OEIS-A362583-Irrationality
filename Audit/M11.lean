import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-! M11: Int.fract arithmetic for the binary-digit pigeonhole (spec §4) -/

-- Basic API (Mathlib/Algebra/Order/Floor/Ring.lean; [Ring R] [LinearOrder R] [FloorRing R],
-- plus [IsOrderedRing R] for the order facts). NOTE: names are *Cast-suffixed in this pin —
-- there is NO `Int.fract_add_int` / `Int.fract_int_add`.
#check @Int.fract_add_intCast   -- fract (a + m) = fract a  (m : ℤ)
#check @Int.fract_intCast_add   -- fract (↑m + a) = fract a
#check @Int.fract_add_natCast   -- fract (a + n) = fract a  (n : ℕ)
#check @Int.fract_add_one       -- fract (a + 1) = fract a
#check @Int.fract_eq_self       -- fract a = a ↔ 0 ≤ a ∧ a < 1
#check @Int.fract_nonneg        -- 0 ≤ fract a
#check @Int.fract_lt_one        -- fract a < 1
#check @Int.fract_fract         -- fract (fract a) = fract a
#check @Int.fract_add           -- ∃ z : ℤ, fract (a + b) - fract a - fract b = z

-- Denominator control for fract of rationals ([Field k] [LinearOrder k] [IsOrderedRing k]
-- [FloorRing k], m : ℤ implicit, n : ℕ implicit):
#check @Int.fract_div_intCast_eq_div_intCast_mod  -- fract ((m : k) / n) = ((m % n : ℤ) : k) / n
#check @Int.fract_div_natCast_eq_div_natCast_mod  -- ℕ-numerator version

-- Denominator fact "fract (2^j * (a/b)) has denominator dividing b": NO new Mathlib lemma
-- needed. Rewrite 2^j * ((a : ℝ)/b) = ((2^j * a : ℤ) : ℝ) / (b : ℕ) by push_cast, then
-- `Int.fract_div_intCast_eq_div_intCast_mod` gives fract = ((2^j * a) % b : ℤ) / b with
-- numerator in [0, b) via Int.emod_nonneg / Int.emod_lt_of_pos. Only casting glue remains;
-- if packaged, the new lemma would be:
--   lemma fract_pow_two_mul_div (j : ℕ) (a : ℤ) (b : ℕ) (hb : b ≠ 0) :
--       Int.fract (2 ^ j * ((a : ℝ) / b)) = ((2 ^ j * a % b : ℤ) : ℝ) / b

example : Int.fract ((7 : ℝ) / 2) = 1 / 2 := by
  rw [show (7 : ℝ) / 2 = ((7 : ℤ) : ℝ) / ((2 : ℕ) : ℝ) by norm_num,
    Int.fract_div_intCast_eq_div_intCast_mod]
  norm_num

-- the pigeonhole move, j = 4, a/b = 3/7: fract (2^4 * (3/7)) = (48 % 7)/7 = 6/7
example : Int.fract (2 ^ 4 * ((3 : ℝ) / 7)) = 6 / 7 := by
  rw [show (2 : ℝ) ^ 4 * (3 / 7) = ((48 : ℤ) : ℝ) / ((7 : ℕ) : ℝ) by norm_num,
    Int.fract_div_intCast_eq_div_intCast_mod]
  norm_num
