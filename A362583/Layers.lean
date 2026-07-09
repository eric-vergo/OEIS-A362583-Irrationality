/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
import A362583.Character
import A362583.Divergence

/-!
# Analysis of the Euler-product layers B and T

Summability, bounds and holomorphy for the layers `layerB`, `layerT` (defined in
`A362583.Character`), plus the logarithm series and the per-prime split feeding the Euler
wiring.  Re-exports `A362583.Character` (the character `χ` and the layer objects) and
`A362583.Divergence` (the blow-up statements), so `import A362583.Layers` still provides the
whole layer API.

* The logarithm series: `hasSum_neg_log_one_sub`, `neg_log_one_sub_eq_tsum`.
* Summability and bounds: `summable_norm_tp`, `summable_tp`, the uniform bound
  `norm_layerT_le` (`‖T(s)‖ ≤ cT`), and `layerBReal_le_cB`, `norm_layerB_le`.
* Real-axis agreement: `layerB_ofReal`, `tp_ofReal`, `layerT_ofReal`, and the `re`/`im`
  lemmas.
* Holomorphy on `Ω = {1/2 < re}`: `differentiableOn_layerT`, `differentiableOn_layerB`.
* Preparation for the Euler wiring: the per-prime split `neg_log_split`, the `layerB`
  identification `tsum_term_two_eq_layerB`, and the three absolute-summability facts
  `summable_norm_term_one`, `summable_norm_term_two`, `summable_norm_tp`.
-/

namespace A362583

open Complex

/-! ## The logarithm series (branch pinned inside Mathlib's `logTaylor` API) -/

/-- `-log(1-z) = Σ_{k≥1} z^k/k` in `HasSum` form.  The `k = 0` term is `0`
(Lean's `z^0/0 = 0`).  Thin wrapper around `Complex.hasSum_taylorSeries_neg_log`;
the branch of `Complex.log` is pinned inside Mathlib's proof, so no separate
exp-inversion argument is needed. -/
lemma hasSum_neg_log_one_sub {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun k : ℕ ↦ z ^ k / k) (-Complex.log (1 - z)) :=
  Complex.hasSum_taylorSeries_neg_log hz

/-- Shifted `tsum` form: `-log(1-z) = Σ_{k≥0} z^(k+1)/(k+1)` for
`‖z‖ ≤ 1/2`. -/
lemma neg_log_one_sub_eq_tsum {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    -Complex.log (1 - z) = ∑' k : ℕ, z ^ (k + 1) / (k + 1) := by
  have h := hasSum_neg_log_one_sub (z := z) (by linarith : ‖z‖ < 1)
  rw [← h.tsum_eq, h.summable.tsum_eq_zero_add]
  simp only [pow_zero, Nat.cast_zero, div_zero, zero_add]
  exact tsum_congr fun k ↦ by push_cast; rfl

/-! ## Summability and bounds for the layers -/

/-- Absolute summability of the complex `layerB` integrand for `Re s > 1/2`. -/
lemma summable_layerB_term {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable (fun p : Nat.Primes ↦ if (p : ℕ) = 2 then 0 else ((p : ℕ) : ℂ) ^ (-(2 * s))) := by
  refine Summable.of_norm_bounded (g := fun p : Nat.Primes ↦ ((p : ℕ) : ℝ) ^ (-(2 * s.re)))
    (Nat.Primes.summable_rpow.mpr (by linarith)) (fun p ↦ ?_)
  rcases eq_or_ne (p : ℕ) 2 with h | h
  · rw [if_pos h, norm_zero]
    positivity
  · rw [if_neg h, Complex.norm_natCast_cpow_of_pos p.prop.pos, neg_two_mul_re]

/-- Geometric-tail norm bound for the shape of `tp`: for `‖z‖ < 1`,
`‖∑' k, z^(k+3)/(k+3)‖ ≤ ‖z‖³·(1-‖z‖)⁻¹/3`.  Each term is dominated by `‖z‖^(k+3)/3`
(since `1/(k+3) ≤ 1/3`) and the resulting geometric series sums in closed form. -/
private lemma norm_tsum_pow_add_three_div_le {z : ℂ} (hz1 : ‖z‖ < 1) :
    ‖∑' k : ℕ, z ^ (k + 3) / ((k + 3 : ℕ) : ℂ)‖ ≤ ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ / 3 := by
  have hterm : ∀ k : ℕ, ‖z ^ (k + 3) / ((k + 3 : ℕ) : ℂ)‖ ≤ ‖z‖ ^ (k + 3) / 3 := by
    intro k
    rw [norm_div, norm_pow, Complex.norm_natCast]
    gcongr
    exact_mod_cast Nat.le_add_left 3 k
  have hgeom0 : Summable (fun k : ℕ ↦ ‖z‖ ^ k) :=
    summable_geometric_of_lt_one (norm_nonneg z) hz1
  have hgeom : Summable (fun k : ℕ ↦ ‖z‖ ^ (k + 3) / 3) := by
    refine Summable.div_const ?_ 3
    exact (hgeom0.mul_left (‖z‖ ^ 3)).congr fun k ↦ by rw [← pow_add, Nat.add_comm 3 k]
  have hnorms : Summable (fun k : ℕ ↦ ‖z ^ (k + 3) / ((k + 3 : ℕ) : ℂ)‖) :=
    Summable.of_nonneg_of_le (fun k ↦ norm_nonneg _) hterm hgeom
  have h1 : ‖∑' k : ℕ, z ^ (k + 3) / ((k + 3 : ℕ) : ℂ)‖ ≤ ∑' k : ℕ, ‖z‖ ^ (k + 3) / 3 :=
    (norm_tsum_le_tsum_norm hnorms).trans (hnorms.tsum_le_tsum hterm hgeom)
  have h2 : ∑' k : ℕ, ‖z‖ ^ (k + 3) / 3 = ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ / 3 := by
    rw [tsum_div_const]
    congr 1
    calc ∑' k : ℕ, ‖z‖ ^ (k + 3) = ∑' k : ℕ, ‖z‖ ^ 3 * ‖z‖ ^ k :=
          tsum_congr fun k ↦ by rw [← pow_add, Nat.add_comm 3 k]
      _ = ‖z‖ ^ 3 * ∑' k : ℕ, ‖z‖ ^ k := tsum_mul_left
      _ = ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ := by rw [tsum_geometric_of_lt_one (norm_nonneg z) hz1]
  rw [h2] at h1
  exact h1

/-- Per-prime bound: `‖t_p(s)‖ ≤ (4/3) p^(-3/2)` on `Re s ≥ 1/2` (geometric tail
with `‖z_p‖ ≤ p^(-1/2) ≤ 2^(-1/2) ≤ 3/4`, so `(1-‖z_p‖)⁻¹ ≤ 4` and `1/(k+3) ≤ 1/3`). -/
lemma norm_tp_le (p : Nat.Primes) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖tp p s‖ ≤ 4 / 3 * ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) := by
  obtain ⟨z, hzdef⟩ : ∃ z : ℂ, z = χ ((p : ℕ) : ZMod 4) * ((p : ℕ) : ℂ) ^ (-s) := ⟨_, rfl⟩
  have htp : tp p s = ∑' k : ℕ, z ^ (k + 3) / ((k + 3 : ℕ) : ℂ) := by rw [hzdef]; rfl
  have hz34 : ‖z‖ ≤ 3 / 4 := by rw [hzdef]; exact norm_χ_mul_cpow_le_three_quarters p hs
  have hzp : ‖z‖ ≤ ((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) := by
    rw [hzdef]; exact norm_χ_mul_cpow_le_rpow_neg_half p hs
  have hz1 : ‖z‖ < 1 := lt_of_le_of_lt hz34 (by norm_num)
  have hinv : (1 - ‖z‖)⁻¹ ≤ 4 := by
    have hx : (0 : ℝ) < 1 - ‖z‖ := by linarith
    rw [← one_div, div_le_iff₀ hx]
    linarith
  have hcube : ‖z‖ ^ 3 ≤ (((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ)) ^ 3 := by
    gcongr
  have hpow : (((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ)) ^ 3 = ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) := by
    rw [← Real.rpow_natCast (((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ)) 3,
      ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num
  calc ‖tp p s‖ = ‖∑' k : ℕ, z ^ (k + 3) / ((k + 3 : ℕ) : ℂ)‖ := by rw [htp]
    _ ≤ ‖z‖ ^ 3 * (1 - ‖z‖)⁻¹ / 3 := norm_tsum_pow_add_three_div_le hz1
    _ ≤ (((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ)) ^ 3 * 4 / 3 := by
        have hbnn : (0 : ℝ) ≤ (1 - ‖z‖)⁻¹ := by
          have hx : (0 : ℝ) < 1 - ‖z‖ := by linarith
          positivity
        have h3 : (0 : ℝ) ≤ (((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ)) ^ 3 := by positivity
        have := mul_le_mul hcube hinv hbnn h3
        linarith
    _ = 4 / 3 * ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) := by rw [hpow]; ring

/-- Absolute summability of `‖t_p(s)‖` over primes on `Re s ≥ 1/2`. -/
lemma summable_norm_tp {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    Summable (fun p : Nat.Primes ↦ ‖tp p s‖) := by
  refine Summable.of_nonneg_of_le (fun p ↦ norm_nonneg _) (fun p ↦ norm_tp_le p hs) ?_
  exact (Nat.Primes.summable_rpow.mpr (by norm_num)).mul_left (4 / 3)

/-- Plain summability of the `layerT` integrand on `Re s ≥ 1/2`. -/
lemma summable_tp {s : ℂ} (hs : 1 / 2 ≤ s.re) : Summable (fun p : Nat.Primes ↦ tp p s) :=
  (summable_norm_tp hs).of_norm

/-- **Uniform bound for `T`**: `‖T(s)‖ ≤ cT` on `Re s ≥ 1/2`. -/
theorem norm_layerT_le {s : ℂ} (hs : 1 / 2 ≤ s.re) : ‖layerT s‖ ≤ cT := by
  unfold layerT cT
  calc ‖∑' p : Nat.Primes, tp p s‖ ≤ ∑' p : Nat.Primes, ‖tp p s‖ :=
        norm_tsum_le_tsum_norm (summable_norm_tp hs)
    _ ≤ ∑' p : Nat.Primes, 4 / 3 * ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) := by
        refine (summable_norm_tp hs).tsum_le_tsum (fun p ↦ norm_tp_le p hs) ?_
        exact (Nat.Primes.summable_rpow.mpr (by norm_num)).mul_left (4 / 3)
    _ = 4 / 3 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) := tsum_mul_left

/-- `0 ≤ layerBReal σ` (unconditional: a non-summable `tsum` is `0`). -/
lemma layerBReal_nonneg (σ : ℝ) : 0 ≤ layerBReal σ := by
  unfold layerBReal
  have h : 0 ≤ ∑' p : Nat.Primes, if (p : ℕ) = 2 then 0 else ((p : ℕ) : ℝ) ^ (-(2 * σ)) :=
    tsum_nonneg fun p ↦ by
      rcases eq_or_ne (p : ℕ) 2 with h | h
      · simp [h]
      · simp only [if_neg h]
        positivity
  linarith

/-- **Bound for `layerBReal`**: `layerBReal σ ≤ cB` for real `σ ≥ 1`. -/
theorem layerBReal_le_cB {σ : ℝ} (hσ : 1 ≤ σ) : layerBReal σ ≤ cB := by
  unfold layerBReal cB
  have h1 : Summable (fun p : Nat.Primes ↦ ((p : ℕ) : ℝ) ^ (-2 : ℝ)) :=
    Nat.Primes.summable_rpow.mpr (by norm_num)
  have h2 := summable_layerBReal_term (by linarith : 1 / 2 < σ)
  have hle : ∀ p : Nat.Primes,
      (if (p : ℕ) = 2 then 0 else ((p : ℕ) : ℝ) ^ (-(2 * σ))) ≤ ((p : ℕ) : ℝ) ^ (-2 : ℝ) := by
    intro p
    rcases eq_or_ne (p : ℕ) 2 with h | h
    · rw [if_pos h]
      positivity
    · rw [if_neg h]
      refine Real.rpow_le_rpow_of_exponent_le ?_ (by linarith)
      exact_mod_cast p.prop.one_lt.le
  have := h2.tsum_le_tsum hle h1
  linarith

/-! ## Real-valuedness on the real axis -/

/-- For real `σ`, `layerB` is the cast of `layerBReal` (unconditional). -/
lemma layerB_ofReal (σ : ℝ) : layerB (σ : ℂ) = ((layerBReal σ : ℝ) : ℂ) := by
  unfold layerB layerBReal
  rw [Complex.ofReal_mul, Complex.ofReal_tsum]
  congr 1
  · norm_num
  · refine tsum_congr fun p ↦ ?_
    rcases eq_or_ne (p : ℕ) 2 with hp | hp
    · simp [hp]
    · rw [if_neg hp, if_neg hp, Complex.ofReal_cpow (Nat.cast_nonneg _)]
      push_cast
      rfl

/-- For real `σ`, `tp` is the cast of `tpReal` (unconditional). -/
lemma tp_ofReal (p : Nat.Primes) (σ : ℝ) : tp p (σ : ℂ) = ((tpReal p σ : ℝ) : ℂ) := by
  unfold tp tpReal
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun k ↦ ?_
  rw [Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_mul,
    Complex.ofReal_cpow (Nat.cast_nonneg _), χ_natCast_eq_kernel]
  push_cast
  rfl

/-- For real `σ`, `layerT` is the cast of `layerTReal` (unconditional). -/
lemma layerT_ofReal (σ : ℝ) : layerT (σ : ℂ) = ((layerTReal σ : ℝ) : ℂ) := by
  unfold layerT layerTReal
  rw [Complex.ofReal_tsum]
  exact tsum_congr fun p ↦ tp_ofReal p σ

/-- `layerB` is real on the real axis. -/
lemma layerB_im (σ : ℝ) : (layerB (σ : ℂ)).im = 0 := by
  rw [layerB_ofReal]; exact Complex.ofReal_im _

/-- Real part of `layerB` on the real axis. -/
lemma layerB_re (σ : ℝ) : (layerB (σ : ℂ)).re = layerBReal σ := by
  rw [layerB_ofReal]; exact Complex.ofReal_re _

/-- `layerT` is real on the real axis. -/
lemma layerT_im (σ : ℝ) : (layerT (σ : ℂ)).im = 0 := by
  rw [layerT_ofReal]; exact Complex.ofReal_im _

/-- Real part of `layerT` on the real axis. -/
lemma layerT_re (σ : ℝ) : (layerT (σ : ℂ)).re = layerTReal σ := by
  rw [layerT_ofReal]; exact Complex.ofReal_re _

/-- `‖layerB σ‖ ≤ cB` for real `σ ≥ 1`. -/
theorem norm_layerB_le {σ : ℝ} (hσ : 1 ≤ σ) : ‖layerB (σ : ℂ)‖ ≤ cB := by
  rw [layerB_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (layerBReal_nonneg σ)]
  exact layerBReal_le_cB hσ

/-- Real-companion bound `|layerTReal σ| ≤ cT` for real `σ ≥ 1/2`. -/
lemma abs_layerTReal_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) : |layerTReal σ| ≤ cT := by
  have h := norm_layerT_le (s := (σ : ℂ)) (by simpa using hσ)
  rw [layerT_ofReal, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-! ## Holomorphy on Ω = {Re s > 1/2} -/

/-- Each `t_p` is holomorphic on `Ω` (M-test with the uniform geometric bound
`(3/4)^k`, valid on all of `Ω`). -/
lemma differentiableOn_tp (p : Nat.Primes) :
    DifferentiableOn ℂ (fun s ↦ tp p s) {s : ℂ | 1 / 2 < s.re} := by
  unfold tp
  have hne : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.prop.pos.ne'
  refine Complex.differentiableOn_tsum_of_summable_norm
    (u := fun k : ℕ ↦ (3 / 4 : ℝ) ^ k)
    (summable_geometric_of_lt_one (by norm_num) (by norm_num)) (fun k ↦ ?_)
    (isOpen_lt continuous_const Complex.continuous_re) (fun k w hw ↦ ?_)
  · have hd : Differentiable ℂ (fun s : ℂ ↦
        (χ ((p : ℕ) : ZMod 4) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 3) / ((k + 3 : ℕ) : ℂ)) := by
      apply Differentiable.div_const
      apply Differentiable.pow
      apply Differentiable.const_mul
      exact Differentiable.const_cpow (differentiable_id.neg) (Or.inl hne)
    exact hd.differentiableOn
  · have hw' : (1 / 2 : ℝ) ≤ w.re := le_of_lt hw
    have h34 := norm_χ_mul_cpow_le_three_quarters p hw'
    rw [norm_div, norm_pow, Complex.norm_natCast]
    calc ‖χ ((p : ℕ) : ZMod 4) * ((p : ℕ) : ℂ) ^ (-w)‖ ^ (k + 3) / ((k + 3 : ℕ) : ℝ)
        ≤ ‖χ ((p : ℕ) : ZMod 4) * ((p : ℕ) : ℂ) ^ (-w)‖ ^ (k + 3) := by
          refine div_le_self (by positivity) ?_
          exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
      _ ≤ (3 / 4 : ℝ) ^ (k + 3) := by gcongr
      _ ≤ (3 / 4 : ℝ) ^ k := pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)

/-- **Holomorphy of `T`**: `T` is holomorphic on `Ω = {Re s > 1/2}` (Weierstrass M-test
with the uniform bound `M_p = (4/3) p^(-3/2)`, valid on all of `Ω`). -/
theorem differentiableOn_layerT :
    DifferentiableOn ℂ (fun s ↦ layerT s) {s : ℂ | 1 / 2 < s.re} := by
  unfold layerT
  refine Complex.differentiableOn_tsum_of_summable_norm
    (u := fun p : Nat.Primes ↦ 4 / 3 * ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ))
    ((Nat.Primes.summable_rpow.mpr (by norm_num)).mul_left (4 / 3))
    (fun p ↦ differentiableOn_tp p) (isOpen_lt continuous_const Complex.continuous_re)
    (fun p w hw ↦ norm_tp_le p (le_of_lt hw))

/-- Auxiliary: `layerB` is holomorphic on each `{Re s > δ}`, `δ > 1/2` (M-test with
the summable bound `p^(-2δ)`, which is uniform there but not on all of `Ω`). -/
private lemma differentiableOn_layerB_aux {δ : ℝ} (hδ : 1 / 2 < δ) :
    DifferentiableOn ℂ (fun s ↦ layerB s) {s : ℂ | δ < s.re} := by
  unfold layerB
  refine (differentiableOn_const _).mul ?_
  refine Complex.differentiableOn_tsum_of_summable_norm
    (u := fun p : Nat.Primes ↦ ((p : ℕ) : ℝ) ^ (-(2 * δ)))
    (Nat.Primes.summable_rpow.mpr (by linarith)) (fun p ↦ ?_)
    (isOpen_lt continuous_const Complex.continuous_re) (fun p w hw ↦ ?_)
  · rcases eq_or_ne (p : ℕ) 2 with h | h
    · simp only [if_pos h]
      exact differentiableOn_const 0
    · simp only [if_neg h]
      have hne : ((p : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr p.prop.pos.ne'
      have hd : Differentiable ℂ (fun s : ℂ ↦ ((p : ℕ) : ℂ) ^ (-(2 * s))) := by
        apply Differentiable.const_cpow ?_ (Or.inl hne)
        fun_prop
      exact hd.differentiableOn
  · rcases eq_or_ne (p : ℕ) 2 with h | h
    · rw [if_pos h, norm_zero]
      positivity
    · rw [if_neg h, Complex.norm_natCast_cpow_of_pos p.prop.pos, neg_two_mul_re]
      refine Real.rpow_le_rpow_of_exponent_le ?_ ?_
      · exact_mod_cast p.prop.one_lt.le
      · have hww : δ < w.re := hw
        linarith

/-- **Holomorphy of `B`**: `B` is holomorphic on `Ω = {Re s > 1/2}`.  No single summable
bound exists on all of `Ω`, so this is the compact-exhaustion / local M-test route:
around each `s₀ ∈ Ω`, work on `{Re s > δ}` with `δ := (1/2 + Re s₀)/2`. -/
theorem differentiableOn_layerB :
    DifferentiableOn ℂ (fun s ↦ layerB s) {s : ℂ | 1 / 2 < s.re} := by
  intro s₀ hs₀
  have hs₀' : (1 / 2 : ℝ) < s₀.re := hs₀
  have h1 : (1 / 2 : ℝ) < (1 / 2 + s₀.re) / 2 := by linarith
  have h2 : (1 / 2 + s₀.re) / 2 < s₀.re := by linarith
  have hU : IsOpen {s : ℂ | (1 / 2 + s₀.re) / 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  exact ((differentiableOn_layerB_aux h1).differentiableAt
    (hU.mem_nhds h2)).differentiableWithinAt

/-! ## Preparation for the Euler wiring: the per-prime split -/

/-- Summing the `k = 2` terms over primes gives exactly `layerB` (via
`χ_sq_eq_ite`; unconditional). -/
lemma tsum_term_two_eq_layerB (s : ℂ) :
    ∑' p : Nat.Primes, χ ((p : ℕ) : ZMod 4) ^ 2 * ((p : ℕ) : ℂ) ^ (-(2 * s)) / 2
      = layerB s := by
  unfold layerB
  rw [← tsum_mul_left]
  refine tsum_congr fun p ↦ ?_
  rw [χ_sq_eq_ite]
  rcases eq_or_ne (p : ℕ) 2 with h | h
  · rw [if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h]
    ring

/-- Absolute summability of the `k = 1` terms for `Re s > 1`
(domination by `p^(-Re s)`). -/
lemma summable_norm_term_one {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes ↦ ‖χ ((p : ℕ) : ZMod 4) * ((p : ℕ) : ℂ) ^ (-s)‖) :=
  Summable.of_nonneg_of_le (fun p ↦ norm_nonneg _) (fun p ↦ norm_χ_mul_cpow_le p s)
    (Nat.Primes.summable_rpow.mpr (by linarith))

/-- Absolute summability of the `k = 2` terms for `Re s > 1/2`
(domination by `p^(-2 Re s)`). -/
lemma summable_norm_term_two {s : ℂ} (hs : 1 / 2 < s.re) :
    Summable
      (fun p : Nat.Primes ↦ ‖χ ((p : ℕ) : ZMod 4) ^ 2 * ((p : ℕ) : ℂ) ^ (-(2 * s)) / 2‖) := by
  refine Summable.of_nonneg_of_le (fun p ↦ norm_nonneg _) (fun p ↦ ?_)
    (Nat.Primes.summable_rpow.mpr (by linarith : -(2 * s.re) < -1))
  rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast_cpow_of_pos p.prop.pos,
    neg_two_mul_re]
  have hχ : ‖χ ((p : ℕ) : ZMod 4)‖ ^ 2 ≤ 1 := by
    have h := norm_χ_le_one ((p : ℕ) : ZMod 4)
    nlinarith [norm_nonneg (χ ((p : ℕ) : ZMod 4))]
  have hpos : (0 : ℝ) ≤ ((p : ℕ) : ℝ) ^ (-(2 * s.re)) := by positivity
  have hnorm2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [hnorm2]
  have hmul : ‖χ ((p : ℕ) : ZMod 4)‖ ^ 2 * ((p : ℕ) : ℝ) ^ (-(2 * s.re))
      ≤ 1 * ((p : ℕ) : ℝ) ^ (-(2 * s.re)) := mul_le_mul_of_nonneg_right hχ hpos
  linarith

/-- **Per-prime split**: for `Re s > 1`,
`-log(1 - χ(p) p^(-s)) = χ(p) p^(-s) + χ(p)² p^(-2s)/2 + t_p(s)`.
Proof: peel three terms off the log series with `Summable.sum_add_tsum_nat_add 3`
+ `Finset.sum_range_succ`; the `k = 0` term is `0`, the tail is definitionally
`tp p s`.  No rearrangement is involved. -/
theorem neg_log_split (p : Nat.Primes) {s : ℂ} (hs : 1 < s.re) :
    -Complex.log (1 - χ ((p : ℕ) : ZMod 4) * ((p : ℕ) : ℂ) ^ (-s))
      = χ ((p : ℕ) : ZMod 4) * ((p : ℕ) : ℂ) ^ (-s)
        + χ ((p : ℕ) : ZMod 4) ^ 2 * ((p : ℕ) : ℂ) ^ (-(2 * s)) / 2
        + tp p s := by
  have hz1 : ‖χ ((p : ℕ) : ZMod 4) * ((p : ℕ) : ℂ) ^ (-s)‖ < 1 :=
    lt_of_le_of_lt (norm_χ_mul_cpow_le_half p hs.le) (by norm_num)
  have h := hasSum_neg_log_one_sub hz1
  rw [← h.tsum_eq, ← h.summable.sum_add_tsum_nat_add 3, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one]
  have h2 : (χ ((p : ℕ) : ZMod 4) * ((p : ℕ) : ℂ) ^ (-s)) ^ 2
      = χ ((p : ℕ) : ZMod 4) ^ 2 * ((p : ℕ) : ℂ) ^ (-(2 * s)) := by
    rw [mul_pow, ← Complex.cpow_nat_mul]
    congr 2
    push_cast
    ring
  have htail : ∑' k : ℕ, (χ ((p : ℕ) : ZMod 4) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 3)
      / ((k + 3 : ℕ) : ℂ) = tp p s := rfl
  rw [h2, htail]
  norm_num

end A362583
