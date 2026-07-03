/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Dirichlet series with bounded partial sums: the by-parts continuation

Let `f : ℕ → ℂ` have partial sums `∑ k ∈ Finset.range (n + 1), f k` (that is, `∑_{k ≤ n} f k`)
bounded in norm by a constant `C`.  The Dirichlet series `∑' n, f n * (n : ℂ) ^ (-s)` need not
converge beyond `1 < s.re`, but Abel summation produces a series that does: the **by-parts
series**

`bpSeries f s = ∑' n, (∑ k ∈ Finset.range (n + 1), f k) * ((n : ℂ) ^ (-s) - ((n + 1 : ℂ)) ^ (-s))`

converges for `0 < s.re` (`summable_bpSeries`), is holomorphic on the half-plane
`{s | 0 < s.re}` (`differentiableOn_bpSeries`), and agrees with the Dirichlet series on
`{s | 1 < s.re}` (`tsum_mul_cpow_neg_eq_bpSeries`) — so it *is* the analytic continuation of
the Dirichlet series.  On the real axis the increments `n^(-σ) - (n+1)^(-σ)` are nonnegative
and telescope, giving the uniform bound `‖bpSeries f σ‖ ≤ C * n₀ ^ (-σ)` when the first `n₀`
partial sums vanish (`norm_bpSeries_le`).

This is item **(D1)** of `PROOF.md` (the by-parts series is the continuation object), stated
for an arbitrary `f : ℕ → ℂ`; only the increment bound (audit item M12, absent from Mathlib)
requires analysis, via the fundamental theorem of calculus.

## Main results

* `Complex.norm_ofReal_cpow_sub_ofReal_cpow_le`: for `r.re ≤ 1` and `0 < a ≤ b`,
  `‖(b : ℂ) ^ r - (a : ℂ) ^ r‖ ≤ ‖r‖ * (b - a) * a ^ (r.re - 1)` (FTC increment bound).
* `Complex.norm_natCast_cpow_sub_add_one_cpow_le`: the specialization
  `‖(n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s)‖ ≤ ‖s‖ * (n : ℝ) ^ (-s.re - 1)` for `1 ≤ n`,
  `-1 ≤ s.re`.
* `Real.natCast_rpow_neg_sub_add_one_nonneg`: `0 ≤ (n : ℝ) ^ (-σ) - ((n : ℝ) + 1) ^ (-σ)` for
  `1 ≤ n`, `0 ≤ σ` (real increments are nonnegative, for telescoping).
* `bpSeries`: the by-parts series.
* `summable_bpSeries`, `hasSum_bpSeries`: convergence of the defining series for `0 < s.re`.
* `differentiableOn_bpSeries`: `DifferentiableOn ℂ (bpSeries f) {s | 0 < s.re}`.
* `norm_bpSeries_le`, `norm_bpSeries_le_const`: for real `σ ≥ 0`, if the partial sums below
  `n₀ ≥ 1` vanish then `‖bpSeries f σ‖ ≤ C * (n₀ : ℝ) ^ (-σ) ≤ C`.
* `tsum_mul_cpow_neg_eq_bpSeries`: `∑' n, f n * (n : ℂ) ^ (-s) = bpSeries f s` for `1 < s.re`.

## Indexing conventions

* The `n`-th partial sum is `∑ k ∈ Finset.range (n + 1), f k`, i.e. the sum over `k ≤ n`.
* The `tsum` in `bpSeries` runs over all of `ℕ`.  No hypothesis `f 0 = 0` is needed anywhere:
  since `(0 : ℂ) ^ (-s) = 0` for `s ≠ 0` (Mathlib's junk value is benign here), the `n = 0`
  term of `bpSeries` is `(f 0) * (0 - 1) = -f 0` on the half-plane, and the `n = 0` term of
  the Dirichlet series is `f 0 * 0 = 0`; the identification
  `tsum_mul_cpow_neg_eq_bpSeries` is exact as stated.
* A caller whose partial sums vanish below some `n₀` (e.g. `f` supported on primes, so that
  the partial sums for `n = 0, 1` vanish and `n₀ = 2`) gets
  `‖bpSeries f σ‖ ≤ C * (n₀ : ℝ) ^ (-σ)` from `norm_bpSeries_le`; the terms of `bpSeries`
  below `n₀` are literally `0`, so `bpSeries` coincides with the series started at `n₀`.
-/

open Filter Topology

namespace Complex

/-- **FTC increment bound** for complex powers of positive reals: if `r.re ≤ 1` and
`0 < a ≤ b`, then `‖(b : ℂ) ^ r - (a : ℂ) ^ r‖ ≤ ‖r‖ * (b - a) * a ^ (r.re - 1)`.
The difference is the integral of the derivative `r * x ^ (r - 1)`, whose norm on `[a, b]`
is at most `‖r‖ * a ^ (r.re - 1)` because `x ↦ x ^ (r.re - 1)` is antitone for
`r.re - 1 ≤ 0`. -/
theorem norm_ofReal_cpow_sub_ofReal_cpow_le {r : ℂ} (hr : r.re ≤ 1) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) : ‖(b : ℂ) ^ r - (a : ℂ) ^ r‖ ≤ ‖r‖ * (b - a) * a ^ (r.re - 1) := by
  rcases eq_or_ne r 0 with rfl | hr0
  · simp
  have hb : 0 < b := ha.trans_le hab
  have hderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun y : ℝ => (y : ℂ) ^ r)
      (r * (x : ℂ) ^ (r - 1)) x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    exact hasDerivAt_ofReal_cpow_const (ha.trans_le hx.1).ne' hr0
  have hint : IntervalIntegrable (fun x : ℝ => r * (x : ℂ) ^ (r - 1))
      MeasureTheory.volume a b :=
    (intervalIntegral.intervalIntegrable_cpow
      (Or.inr (Set.notMem_uIcc_of_lt ha hb))).const_mul r
  have hFTC : (∫ y in a..b, r * (y : ℂ) ^ (r - 1)) = (b : ℂ) ^ r - (a : ℂ) ^ r :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [← hFTC]
  have hbound : ∀ x ∈ Set.uIoc a b, ‖r * (x : ℂ) ^ (r - 1)‖ ≤ ‖r‖ * a ^ (r.re - 1) := by
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos (ha.trans hx.1)]
    have hre : (r - 1).re = r.re - 1 := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos ha hx.1.le (by linarith)) (norm_nonneg r)
  calc ‖∫ x in a..b, r * (x : ℂ) ^ (r - 1)‖
      ≤ ‖r‖ * a ^ (r.re - 1) * |b - a| :=
        intervalIntegral.norm_integral_le_of_norm_le_const hbound
    _ = ‖r‖ * (b - a) * a ^ (r.re - 1) := by
        rw [abs_of_nonneg (sub_nonneg.2 hab)]; ring

/-- **Increment bound for Dirichlet weights** (audit item M12, PROOF.md D1): for `1 ≤ n` and
`-1 ≤ s.re`, `‖(n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s)‖ ≤ ‖s‖ * (n : ℝ) ^ (-s.re - 1)`.
This is `Complex.norm_ofReal_cpow_sub_ofReal_cpow_le` at `r = -s`, `[a, b] = [n, n + 1]`. -/
theorem norm_natCast_cpow_sub_add_one_cpow_le {s : ℂ} (hs : -1 ≤ s.re) {n : ℕ} (hn : 1 ≤ n) :
    ‖(n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s)‖ ≤ ‖s‖ * (n : ℝ) ^ (-s.re - 1) := by
  have hn' : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
  have h := norm_ofReal_cpow_sub_ofReal_cpow_le (r := -s)
    (by rw [neg_re]; linarith) hn' (le_add_of_nonneg_right zero_le_one)
  rw [norm_sub_rev] at h
  simpa [add_sub_cancel_left] using h

end Complex

namespace Real

/-- For `0 ≤ σ` and `1 ≤ n` the increments `(n : ℝ) ^ (-σ) - ((n : ℝ) + 1) ^ (-σ)` of the
antitone map `n ↦ n ^ (-σ)` are nonnegative; they telescope to `(n₀ : ℝ) ^ (-σ)` when summed
over `n ≥ n₀ ≥ 1` (used in `norm_bpSeries_le`). -/
theorem natCast_rpow_neg_sub_add_one_nonneg {σ : ℝ} (hσ : 0 ≤ σ) {n : ℕ} (hn : 1 ≤ n) :
    0 ≤ (n : ℝ) ^ (-σ) - ((n : ℝ) + 1) ^ (-σ) :=
  sub_nonneg.2 <|
    rpow_le_rpow_of_nonpos (Nat.cast_pos.2 hn) (le_add_of_nonneg_right zero_le_one)
      (neg_nonpos.2 hσ)

end Real

/-- The **by-parts series** attached to `f : ℕ → ℂ`:

`bpSeries f s = ∑' n, (∑ k ∈ Finset.range (n + 1), f k) * ((n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s))`.

If the partial sums `∑ k ∈ Finset.range (n + 1), f k = ∑_{k ≤ n} f k` are bounded, this
series converges and is holomorphic on `{s | 0 < s.re}` (`differentiableOn_bpSeries`) and it
agrees with the Dirichlet series `∑' n, f n * (n : ℂ) ^ (-s)` for `1 < s.re`
(`tsum_mul_cpow_neg_eq_bpSeries`): it is the analytic continuation of that Dirichlet series
to the right half-plane.  This is PROOF.md's continuation object `Ã` (item D1). -/
noncomputable def bpSeries (f : ℕ → ℂ) (s : ℂ) : ℂ :=
  ∑' n : ℕ, (∑ k ∈ Finset.range (n + 1), f k) * ((n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s))

variable {f : ℕ → ℂ} {C : ℝ}

/-- If the partial sums of `f` are bounded by `C`, the series defining `bpSeries f s`
converges absolutely for `0 < s.re`: its terms are `O (n ^ (-s.re - 1))` by the increment
bound `Complex.norm_natCast_cpow_sub_add_one_cpow_le`. -/
theorem summable_bpSeries (hC : ∀ n, ‖∑ k ∈ Finset.range (n + 1), f k‖ ≤ C) {s : ℂ}
    (hs : 0 < s.re) :
    Summable fun n : ℕ =>
      (∑ k ∈ Finset.range (n + 1), f k) * ((n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s)) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine Summable.of_norm_bounded_eventually_nat
    (g := fun n : ℕ => C * ‖s‖ * (n : ℝ) ^ (-s.re - 1))
    ((Real.summable_nat_rpow.2 (by linarith)).mul_left _) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [norm_mul]
  calc ‖∑ k ∈ Finset.range (n + 1), f k‖ * ‖(n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s)‖
      ≤ C * (‖s‖ * (n : ℝ) ^ (-s.re - 1)) :=
        mul_le_mul (hC n) (Complex.norm_natCast_cpow_sub_add_one_cpow_le (by linarith) hn)
          (norm_nonneg _) hC0
    _ = C * ‖s‖ * (n : ℝ) ^ (-s.re - 1) := (mul_assoc _ _ _).symm

/-- `HasSum` form of `summable_bpSeries`. -/
theorem hasSum_bpSeries (hC : ∀ n, ‖∑ k ∈ Finset.range (n + 1), f k‖ ≤ C) {s : ℂ}
    (hs : 0 < s.re) :
    HasSum
      (fun n : ℕ =>
        (∑ k ∈ Finset.range (n + 1), f k) * ((n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s)))
      (bpSeries f s) :=
  (summable_bpSeries hC hs).hasSum

/-- **Bounded partial sums give a holomorphic by-parts series** (PROOF.md D1): if
`‖∑ k ∈ Finset.range (n + 1), f k‖ ≤ C` for all `n`, then `bpSeries f` is holomorphic on the
open right half-plane `{s | 0 < s.re}`.

Consumers needing a smaller half-plane `{s | δ < s.re}` (e.g. `δ = 1/2`) can compose with
`DifferentiableOn.mono`.  The proof applies the Weierstrass `M`-test
(`Complex.differentiableOn_tsum_of_summable_norm`) on a small open box
`{s | δ < s.re} ∩ ball 0 R` around each point, where the terms satisfy the single summable
bound `C * R * n ^ (-δ - 1)`. -/
theorem differentiableOn_bpSeries (hC : ∀ n, ‖∑ k ∈ Finset.range (n + 1), f k‖ ≤ C) :
    DifferentiableOn ℂ (bpSeries f) {s : ℂ | 0 < s.re} := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  intro s₀ hs₀
  have hs₀re : 0 < s₀.re := hs₀
  obtain ⟨δ, hδ, hδs₀⟩ : ∃ δ : ℝ, 0 < δ ∧ δ < s₀.re :=
    ⟨s₀.re / 2, half_pos hs₀re, half_lt_self hs₀re⟩
  obtain ⟨R, hR, hs₀R⟩ : ∃ R : ℝ, 1 ≤ R ∧ ‖s₀‖ < R :=
    ⟨‖s₀‖ + 1, le_add_of_nonneg_left (norm_nonneg _), lt_add_one _⟩
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hVopen : IsOpen ({s : ℂ | δ < s.re} ∩ Metric.ball 0 R) :=
    (isOpen_lt continuous_const Complex.continuous_re).inter Metric.isOpen_ball
  have hs₀V : s₀ ∈ {s : ℂ | δ < s.re} ∩ Metric.ball 0 R :=
    ⟨hδs₀, by rw [Metric.mem_ball, dist_zero_right]; exact hs₀R⟩
  -- summable uniform bound on the box
  have hu : Summable (fun n : ℕ => if n = 0 then C else C * R * (n : ℝ) ^ (-δ - 1)) := by
    refine Summable.of_norm_bounded_eventually_nat
      (g := fun n : ℕ => C * R * (n : ℝ) ^ (-δ - 1))
      ((Real.summable_nat_rpow.2 (by linarith)).mul_left _) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [if_neg (Nat.one_le_iff_ne_zero.mp hn), Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (mul_nonneg hC0 hR0) (Real.rpow_nonneg (Nat.cast_nonneg n) _))]
  -- each term is holomorphic on the box
  have hFdiff : ∀ n : ℕ, DifferentiableOn ℂ
      (fun s : ℂ =>
        (∑ k ∈ Finset.range (n + 1), f k) * ((n : ℂ) ^ (-s) - ((n : ℂ) + 1) ^ (-s)))
      ({s : ℂ | δ < s.re} ∩ Metric.ball 0 R) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · -- `n = 0`: on the box the term is the constant `(f 0) * (0 - 1)`
      refine (differentiableOn_const ((∑ k ∈ Finset.range (0 + 1), f k) * (0 - 1))).congr ?_
      intro w hw
      have hw0 : -w ≠ 0 := by
        rw [ne_eq, neg_eq_zero]
        rintro rfl
        have : δ < (0 : ℂ).re := hw.1
        rw [Complex.zero_re] at this
        linarith
      simp [Complex.zero_cpow hw0]
    · have hne : ((n : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      have hne1 : ((n : ℕ) : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
      exact (((differentiable_neg.const_cpow (Or.inl hne)).sub
        (differentiable_neg.const_cpow (Or.inl hne1))).const_mul _).differentiableOn
  -- the terms satisfy the uniform bound on the box
  have hFle : ∀ (n : ℕ) (w : ℂ), w ∈ {s : ℂ | δ < s.re} ∩ Metric.ball 0 R →
      ‖(∑ k ∈ Finset.range (n + 1), f k) * ((n : ℂ) ^ (-w) - ((n : ℂ) + 1) ^ (-w))‖ ≤
        (if n = 0 then C else C * R * (n : ℝ) ^ (-δ - 1)) := by
    intro n w hw
    have hwre : δ < w.re := hw.1
    have hwnorm : ‖w‖ < R := by
      have := hw.2
      rwa [Metric.mem_ball, dist_zero_right] at this
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [if_pos rfl]
      have hw0 : -w ≠ 0 := by
        rw [ne_eq, neg_eq_zero]
        rintro rfl
        rw [Complex.zero_re] at hwre
        linarith
      simpa [Complex.zero_cpow hw0] using hC 0
    · rw [if_neg hn.ne']
      have h1n : (1 : ℝ) ≤ (n : ℝ) := Nat.one_le_cast.2 hn
      rw [norm_mul]
      calc ‖∑ k ∈ Finset.range (n + 1), f k‖ * ‖(n : ℂ) ^ (-w) - ((n : ℂ) + 1) ^ (-w)‖
          ≤ C * (‖w‖ * (n : ℝ) ^ (-w.re - 1)) :=
            mul_le_mul (hC n)
              (Complex.norm_natCast_cpow_sub_add_one_cpow_le (by linarith) hn)
              (norm_nonneg _) hC0
        _ ≤ C * (R * (n : ℝ) ^ (-δ - 1)) := by
            refine mul_le_mul_of_nonneg_left ?_ hC0
            exact mul_le_mul hwnorm.le
              (Real.rpow_le_rpow_of_exponent_le h1n (by linarith))
              (Real.rpow_nonneg (Nat.cast_nonneg n) _) hR0
        _ = C * R * (n : ℝ) ^ (-δ - 1) := (mul_assoc _ _ _).symm
  have hdiff := Complex.differentiableOn_tsum_of_summable_norm hu hFdiff hVopen hFle
  exact ((hdiff s₀ hs₀V).differentiableAt (hVopen.mem_nhds hs₀V)).differentiableWithinAt

/-- **Real-segment bound** (PROOF.md D1, real-axis telescoping): if the partial sums of `f`
are bounded by `C` and vanish for `n < n₀` (with `1 ≤ n₀`), then for real `σ ≥ 0`

`‖bpSeries f σ‖ ≤ C * (n₀ : ℝ) ^ (-σ)`.

For real exponents the increments `n ^ (-σ) - (n + 1) ^ (-σ)` are nonnegative and telescope,
starting at `n₀` because the earlier terms vanish.  (For the race-sum application: partial
sums over `k ≤ 0` and `k ≤ 1` vanish since there are no primes below `2`, so `n₀ = 2` and
the bound is `C * 2 ^ (-σ)`.) -/
theorem norm_bpSeries_le (hC : ∀ n, ‖∑ k ∈ Finset.range (n + 1), f k‖ ≤ C) {n₀ : ℕ}
    (hn₀ : 1 ≤ n₀) (hvanish : ∀ n < n₀, ∑ k ∈ Finset.range (n + 1), f k = 0) {σ : ℝ}
    (hσ : 0 ≤ σ) : ‖bpSeries f σ‖ ≤ C * (n₀ : ℝ) ^ (-σ) := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  -- telescoping majorant
  set G : ℕ → ℝ := fun n => ((max n n₀ : ℕ) : ℝ) ^ (-σ) with hG
  have hterm : ∀ n : ℕ,
      ‖(∑ k ∈ Finset.range (n + 1), f k) *
        ((n : ℂ) ^ (-(σ : ℂ)) - ((n : ℂ) + 1) ^ (-(σ : ℂ)))‖ ≤ C * (G n - G (n + 1)) := by
    intro n
    rcases lt_or_ge n n₀ with hlt | hle
    · rw [hvanish n hlt, zero_mul, norm_zero]
      have h1 : max n n₀ = n₀ := max_eq_right hlt.le
      have h2 : max (n + 1) n₀ = n₀ := max_eq_right (by omega)
      have hzero : G n - G (n + 1) = 0 := by
        rw [hG]
        simp only [h1, h2, sub_self]
      simp [hzero]
    · have hn1 : 1 ≤ n := hn₀.trans hle
      have hGn : G n = (n : ℝ) ^ (-σ) := by
        rw [hG]
        simp only [max_eq_left hle]
      have hGn1 : G (n + 1) = ((n : ℝ) + 1) ^ (-σ) := by
        rw [hG]
        simp only [max_eq_left (show n₀ ≤ n + 1 by omega), Nat.cast_add, Nat.cast_one]
      have hinc : ‖(n : ℂ) ^ (-(σ : ℂ)) - ((n : ℂ) + 1) ^ (-(σ : ℂ))‖
          = (n : ℝ) ^ (-σ) - ((n : ℝ) + 1) ^ (-σ) := by
        have e1 : (n : ℂ) ^ (-(σ : ℂ)) = (((n : ℝ) ^ (-σ) : ℝ) : ℂ) := by
          rw [← Complex.ofReal_natCast n, ← Complex.ofReal_neg σ]
          exact (Complex.ofReal_cpow (Nat.cast_nonneg n) (-σ)).symm
        have e2 : ((n : ℂ) + 1) ^ (-(σ : ℂ)) = ((((n : ℝ) + 1) ^ (-σ) : ℝ) : ℂ) := by
          rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; ring,
            ← Complex.ofReal_neg σ]
          exact (Complex.ofReal_cpow (by positivity) (-σ)).symm
        rw [e1, e2, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact abs_of_nonneg (Real.natCast_rpow_neg_sub_add_one_nonneg hσ hn1)
      rw [norm_mul, hinc, hGn, hGn1]
      exact mul_le_mul_of_nonneg_right (hC n)
        (Real.natCast_rpow_neg_sub_add_one_nonneg hσ hn1)
  have hpartial : ∀ N : ℕ,
      ∑ n ∈ Finset.range N,
        ‖(∑ k ∈ Finset.range (n + 1), f k) *
          ((n : ℂ) ^ (-(σ : ℂ)) - ((n : ℂ) + 1) ^ (-(σ : ℂ)))‖ ≤ C * (n₀ : ℝ) ^ (-σ) := by
    intro N
    have hG0 : G 0 = (n₀ : ℝ) ^ (-σ) := by
      rw [hG]
      simp only [Nat.zero_max]
    have hGN : 0 ≤ G N := Real.rpow_nonneg (Nat.cast_nonneg _) _
    calc ∑ n ∈ Finset.range N,
          ‖(∑ k ∈ Finset.range (n + 1), f k) *
            ((n : ℂ) ^ (-(σ : ℂ)) - ((n : ℂ) + 1) ^ (-(σ : ℂ)))‖
        ≤ ∑ n ∈ Finset.range N, C * (G n - G (n + 1)) :=
          Finset.sum_le_sum fun n _ => hterm n
      _ = C * (G 0 - G N) := by rw [← Finset.mul_sum, Finset.sum_range_sub' G N]
      _ ≤ C * (n₀ : ℝ) ^ (-σ) := by
          rw [← hG0]
          exact mul_le_mul_of_nonneg_left (sub_le_self _ hGN) hC0
  have hnormsum : Summable fun n : ℕ =>
      ‖(∑ k ∈ Finset.range (n + 1), f k) *
        ((n : ℂ) ^ (-(σ : ℂ)) - ((n : ℂ) + 1) ^ (-(σ : ℂ)))‖ :=
    summable_of_sum_range_le (fun n => norm_nonneg _) hpartial
  calc ‖bpSeries f σ‖
      ≤ ∑' n : ℕ, ‖(∑ k ∈ Finset.range (n + 1), f k) *
          ((n : ℂ) ^ (-(σ : ℂ)) - ((n : ℂ) + 1) ^ (-(σ : ℂ)))‖ :=
        norm_tsum_le_tsum_norm hnormsum
    _ ≤ C * (n₀ : ℝ) ^ (-σ) :=
        Real.tsum_le_of_sum_range_le (fun n => norm_nonneg _) hpartial

/-- Convenience form of `norm_bpSeries_le`: under the same hypotheses,
`‖bpSeries f σ‖ ≤ C` (since `(n₀ : ℝ) ^ (-σ) ≤ 1`). -/
theorem norm_bpSeries_le_const (hC : ∀ n, ‖∑ k ∈ Finset.range (n + 1), f k‖ ≤ C) {n₀ : ℕ}
    (hn₀ : 1 ≤ n₀) (hvanish : ∀ n < n₀, ∑ k ∈ Finset.range (n + 1), f k = 0) {σ : ℝ}
    (hσ : 0 ≤ σ) : ‖bpSeries f σ‖ ≤ C := by
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  refine (norm_bpSeries_le hC hn₀ hvanish hσ).trans ?_
  calc C * (n₀ : ℝ) ^ (-σ) ≤ C * 1 :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_one_of_one_le_of_nonpos (Nat.one_le_cast.2 hn₀) (neg_nonpos.2 hσ))
          hC0
    _ = C := mul_one C

/-- **Identification with the Dirichlet series** (PROOF.md D1): if the partial sums of `f`
are bounded by `C`, then for `1 < s.re`

`∑' n, f n * (n : ℂ) ^ (-s) = bpSeries f s`.

Both series converge (the coefficients satisfy `‖f n‖ ≤ 2 * C`); the finite Abel summation
`Finset.sum_range_by_parts` relates their partial sums, and the boundary term
`(∑ k ≤ N, f k) * (N : ℂ) ^ (-s)` tends to `0` since `‖(N : ℂ) ^ (-s)‖ = N ^ (-s.re) → 0`.
No hypothesis on `f 0` is needed: the `n = 0` Dirichlet term vanishes because
`(0 : ℂ) ^ (-s) = 0` for `s ≠ 0`. -/
theorem tsum_mul_cpow_neg_eq_bpSeries (hC : ∀ n, ‖∑ k ∈ Finset.range (n + 1), f k‖ ≤ C)
    {s : ℂ} (hs : 1 < s.re) : ∑' n : ℕ, f n * (n : ℂ) ^ (-s) = bpSeries f s := by
  have hs0 : 0 < s.re := zero_lt_one.trans hs
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  -- coefficient bound from bounded partial sums
  have hcoef : ∀ n, ‖f n‖ ≤ 2 * C := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have h := hC 0
      simp only [zero_add, Finset.range_one, Finset.sum_singleton] at h
      linarith
    · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
      have h3 : f (m + 1) =
          (∑ k ∈ Finset.range (m + 1 + 1), f k) - ∑ k ∈ Finset.range (m + 1), f k := by
        rw [Finset.sum_range_succ]; ring
      rw [h3]
      calc ‖(∑ k ∈ Finset.range (m + 1 + 1), f k) - ∑ k ∈ Finset.range (m + 1), f k‖
          ≤ ‖∑ k ∈ Finset.range (m + 1 + 1), f k‖ + ‖∑ k ∈ Finset.range (m + 1), f k‖ :=
            norm_sub_le _ _
        _ ≤ 2 * C := by have := hC (m + 1); have := hC m; linarith
  -- the Dirichlet series converges for `1 < s.re`
  have hD : Summable fun n : ℕ => f n * (n : ℂ) ^ (-s) := by
    refine Summable.of_norm_bounded_eventually_nat
      (g := fun n : ℕ => 2 * C * (n : ℝ) ^ (-s.re))
      ((Real.summable_nat_rpow.2 (by linarith)).mul_left _) ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]
    exact mul_le_mul_of_nonneg_right (hcoef n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  -- finite Abel summation, `Finset.sum_range_by_parts` with the weights as scalars
  have key : ∀ N : ℕ,
      ∑ i ∈ Finset.range (N + 1), f i * (i : ℂ) ^ (-s)
        = (∑ i ∈ Finset.range (N + 1), f i) * (N : ℂ) ^ (-s)
          + ∑ i ∈ Finset.range N,
              (∑ k ∈ Finset.range (i + 1), f k) *
                ((i : ℂ) ^ (-s) - ((i : ℂ) + 1) ^ (-s)) := by
    intro N
    have h := Finset.sum_range_by_parts (fun i : ℕ => (i : ℂ) ^ (-s)) f (N + 1)
    simp only [smul_eq_mul, Nat.add_sub_cancel] at h
    have step1 : ∑ i ∈ Finset.range (N + 1), f i * (i : ℂ) ^ (-s)
        = ∑ i ∈ Finset.range (N + 1), (i : ℂ) ^ (-s) * f i :=
      Finset.sum_congr rfl fun i _ => mul_comm _ _
    rw [step1, h, sub_eq_add_neg, ← Finset.sum_neg_distrib, mul_comm ((N : ℂ) ^ (-s))]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    rw [← neg_mul, neg_sub, mul_comm]
  -- limits of both sides of the finite identity
  have h1 : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range (N + 1), f i * (i : ℂ) ^ (-s)) atTop
      (𝓝 (∑' n : ℕ, f n * (n : ℂ) ^ (-s))) :=
    hD.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have h2 : Tendsto (fun N : ℕ => (∑ i ∈ Finset.range (N + 1), f i) * (N : ℂ) ^ (-s)) atTop
      (𝓝 0) := by
    refine squeeze_zero_norm (a := fun N : ℕ => C * (N : ℝ) ^ (-s.re)) (fun N => ?_) ?_
    · rw [norm_mul,
        Complex.norm_natCast_cpow_of_re_ne_zero N
          (by rw [Complex.neg_re]; exact neg_ne_zero.2 hs0.ne'),
        Complex.neg_re]
      exact mul_le_mul_of_nonneg_right (hC N) (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    · have h := ((tendsto_rpow_neg_atTop hs0).comp
        (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul C
      rw [mul_zero] at h
      exact h
  have h3 : Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N,
      (∑ k ∈ Finset.range (i + 1), f k) * ((i : ℂ) ^ (-s) - ((i : ℂ) + 1) ^ (-s))) atTop
      (𝓝 (bpSeries f s)) :=
    (hasSum_bpSeries hC hs0).tendsto_sum_nat
  have h4 := h2.add h3
  rw [zero_add] at h4
  exact tendsto_nhds_unique h1 (h4.congr fun N => (key N).symm)

