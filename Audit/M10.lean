import Mathlib.Algebra.BigOperators.Module
import Mathlib.NumberTheory.AbelSummation

/-! M10: summation by parts, discrete and integral (spec §4) -/

-- DISCRETE (Mathlib/Algebra/BigOperators/Module.lean). Stated with `•`;
-- [Ring R] [AddCommGroup M] [Module R M], f : ℕ → R, g : ℕ → M, G n := ∑ i ∈ range n, g i.
#check @Finset.sum_Ioc_by_parts
-- (hmn : m < n) : ∑ i ∈ Ioc m n, f i • g i
--   = f n • G (n+1) - f (m+1) • G (m+1) - ∑ i ∈ Ioc m (n-1), (f (i+1) - f i) • G (i+1)
#check @Finset.sum_range_by_parts
-- ∑ i ∈ range n, f i • g i = f (n-1) • G n - ∑ i ∈ range (n-1), (f (i+1) - f i) • G (i+1)
#check @Finset.sum_Ico_by_parts

-- INTEGRAL (Mathlib/NumberTheory/AbelSummation.lean). [RCLike 𝕜], c : ℕ → 𝕜, f : ℝ → 𝕜.
-- Side conditions, plain form: 0 ≤ a, a ≤ b, ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ f t,
-- IntegrableOn (deriv f) (Set.Icc a b). Floor plumbing: sums are ∑ k ∈ Icc 0 ⌊·⌋₊, c k and
-- the integrand is deriv f t * ∑ k ∈ Icc 0 ⌊t⌋₊, c k over Set.Ioc a b.
#check @sum_mul_eq_sub_sub_integral_mul    -- general a ≤ b
#check @sum_mul_eq_sub_sub_integral_mul'   -- endpoints n m : ℕ (h : n ≤ m), floors erased
#check @sum_mul_eq_sub_integral_mul        -- a = 0; hypotheses on Icc 0 b (0 is IN the interval!)
#check @sum_mul_eq_sub_integral_mul₀       -- extra `c 0 = 0`; hypotheses shrink to Icc 1 b
#check @sum_mul_eq_sub_integral_mul₁       -- extra `c 0 = c 1 = 0`; hypotheses on Icc 2 b
#check @tendsto_sum_mul_atTop_nhds_one_sub_integral
-- b → ∞ version: DifferentiableAt on Set.Ici 0, LocallyIntegrableOn (deriv f) (Ici 0),
-- Tendsto (fun n ↦ f n * ∑ k ∈ Icc 0 n, c k) atTop (𝓝 l), =O[atTop] domination by an
-- IntegrableAtFilter g. `₀` variant: c 0 = 0 and Ici 1 instead of Ici 0.
#check @summable_mul_of_bigO_atTop         -- Summable (fun n ↦ f n * c n) from bigO data
#check @summable_mul_of_bigO_atTop'        -- same but hypotheses on Ici 1 (avoids 0)

-- Route note for weight f = fun y : ℝ ↦ (y : ℂ) ^ (-s) (or rpow on ℝ) against prime-indicator
-- coefficients c: c 0 = c 1 = 0 (0, 1 not prime), so `sum_mul_eq_sub_integral_mul₁` applies with
-- all analytic hypotheses on Icc 2 b where y ≥ 2 > 0 — DifferentiableAt via
-- hasDerivAt_ofReal_cpow_const and IntegrableOn (deriv f) via continuity, no singularity issues.
-- Discrete route needs NO analytic side conditions at all, but leaves a sum of increments
-- f (i+1) - f i to bound by hand (M12 increment lemma). Integral route trades that for the
-- differentiability/integrability conditions above and floor bookkeeping.

-- `•` reduces to `*` over ℝ:
example (f g : ℕ → ℝ) {m n : ℕ} (hmn : m < n) :
    ∑ i ∈ Finset.Ioc m n, f i * g i =
      f n * (∑ j ∈ Finset.range (n + 1), g j) - f (m + 1) * (∑ j ∈ Finset.range (m + 1), g j) -
        ∑ i ∈ Finset.Ioc m (n - 1), (f (i + 1) - f i) * ∑ j ∈ Finset.range (i + 1), g j := by
  simpa only [smul_eq_mul] using Finset.sum_Ioc_by_parts f g hmn
