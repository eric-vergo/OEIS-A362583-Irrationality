import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! M12: norms of n^(-s) and the cpow increment bound (spec §4) -/

-- Norm identities (Mathlib/Analysis/SpecialFunctions/Pow/Real.lean, namespace Complex):
#check @Complex.norm_natCast_cpow_of_pos        -- (hn : 0 < n) (s) : ‖(n:ℂ)^s‖ = (n:ℝ)^s.re
#check @Complex.norm_natCast_cpow_of_re_ne_zero -- (n) (hs : s.re ≠ 0) : same, allows n = 0
#check @Complex.norm_cpow_eq_rpow_re_of_pos     -- (hx : 0 < x) (y) : ‖(x:ℂ)^y‖ = x ^ y.re
#check @Complex.norm_cpow_eq_rpow_re_of_nonneg  -- (hx : 0 ≤ x) (hy : y.re ≠ 0)
#check @Complex.norm_natCast_cpow_pos_of_pos    -- (hn : 0 < n) (s) : 0 < ‖(n:ℂ)^s‖

-- smoke test: ‖2^(-2)‖ = 1/4
example : ‖(2 : ℂ) ^ (-2 : ℂ)‖ = 1 / 4 := by
  have h := Complex.norm_natCast_cpow_of_pos (n := 2) (by norm_num) (-2 : ℂ)
  rw [show ((2 : ℕ) : ℂ) = (2 : ℂ) by norm_num] at h
  rw [h, show ((-2 : ℂ)).re = ((-2 : ℤ) : ℝ) by simp, Real.rpow_intCast]
  norm_num

-- INCREMENT BOUND ‖(n:ℂ)^(-s) - ((n+1):ℂ)^(-s)‖ ≤ ‖s‖ * (n:ℝ)^(-s.re - 1) : ABSENT.
-- Verified: grep over pinned Mathlib source (no cpow/rpow difference-norm inequality) and
-- Loogle `‖_ ^ _ - _ ^ _‖ ≤ _` → 0 hits; `Complex.cpow, HSub.hSub, Norm.norm, LE.le` → 0 hits.
-- New-lemma FTC route (all ingredients below exist):
--  1. ((n+1):ℂ)^(-s) - (n:ℂ)^(-s) = ∫ x in n..(n+1), (-s) * (x:ℝ)^(-s-1)
--     via `intervalIntegral.integral_eq_sub_of_hasDerivAt` + `hasDerivAt_ofReal_cpow_const`
--     (needs x ≠ 0 on [n, n+1], i.e. n ≥ 1, and -s ≠ 0).
--  2. pointwise: ‖(-s) * (x:ℝ)^(-s-1)‖ = ‖s‖ * x^(-s.re-1) by norm_mul +
--     `Complex.norm_cpow_eq_rpow_re_of_pos`; then ≤ ‖s‖ * n^(-s.re-1) for x ∈ [n, n+1]
--     by `Real.rpow_le_rpow_of_nonpos` (base-antitone, exponent ≤ 0; need s.re ≥ -1... use
--     hypothesis 0 < s.re so -s.re - 1 ≤ 0 holds automatically).
--  3. `intervalIntegral.norm_integral_le_of_norm_le_const` with |b - a| = 1.
-- Real-weight analogue uses `Real.hasDerivAt_rpow_const` / `Real.deriv_rpow_const` instead.
#check @hasDerivAt_ofReal_cpow_const
-- (hx : x ≠ 0) (hr : r ≠ 0) : HasDerivAt (fun y : ℝ ↦ (y:ℂ) ^ r) (r * x ^ (r - 1)) x  [root ns]
#check @hasDerivAt_ofReal_cpow_const'   -- antiderivative form, needs r ≠ -1
#check @Complex.deriv_ofReal_cpow_const -- deriv (fun x : ℝ ↦ (x:ℂ)^c) x = c * x^(c-1)
#check @Real.hasDerivAt_rpow_const      -- (h : x ≠ 0 ∨ 1 ≤ p) : HasDerivAt (·^p) (p*x^(p-1)) x
#check @Real.deriv_rpow_const           -- unconditional: deriv (·^p) x = p * x^(p-1)
#check @Real.rpow_le_rpow_of_nonpos     -- (0 < x) (x ≤ y) (z ≤ 0) : y^z ≤ x^z
#check @intervalIntegral.integral_eq_sub_of_hasDerivAt
#check @intervalIntegral.norm_integral_le_of_norm_le_const
-- (h : ∀ x ∈ Ι a b, ‖f x‖ ≤ C) : ‖∫ x in a..b, f x‖ ≤ C * |b - a|
