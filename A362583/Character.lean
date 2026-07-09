/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
import A362583.Defs
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.SumPrimeReciprocals

/-!
# The Dirichlet character χ mod 4 and the Euler-product layers

The mod-4 Dirichlet character `χ` and the analytic objects built from it, shared by the
divergence transfer (`A362583.Divergence`) and the layer analysis (`A362583.Layers`):

* `A362583.χ` — the project Dirichlet character mod 4 (`ZMod.χ₄` pushed to `ℂ`), with value
  lemmas and the elementary bridge `χ_natCast_eq_kernel` / `χ_natCast_eq_ite` to `raceSum`'s
  integrand `raceKernel`.
* Norm estimates for the Euler factors `χ(p) p^(-s)`: `norm_χ_mul_cpow_le` and the crude
  `3/4`, `1/2`, `p^(-1/2)` bounds on the relevant half-planes.
* The Euler-product layer objects: the `k ≥ 3` tail `tp`, the layers `layerT` and `layerB`,
  their real companions `layerBReal`, `tpReal`, `layerTReal`, and the explicit bounds `cB`,
  `cT`.  The value and summability/holomorphy lemmas for these objects live in
  `A362583.Layers`.
-/

namespace A362583

open Complex

/-! ## The character χ -/

/-- The project Dirichlet character mod 4, `ZMod.χ₄` pushed to `ℂ`. -/
noncomputable def χ : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

/-- `χ ≠ 1` (they differ at `3`, a unit of `ZMod 4`). -/
lemma χ_ne_one : χ ≠ 1 := by
  refine (MulChar.ringHomComp_ne_one_iff (Int.castRingHom ℂ).injective_int).mpr ?_
  intro h
  have h3 : (1 : MulChar (ZMod 4) ℤ) ((3 : ℕ) : ZMod 4) = -1 :=
    h ▸ ZMod.χ₄_nat_three_mod_four (by norm_num)
  rw [MulChar.one_apply (IsUnit.of_mul_eq_one 3 (by decide))] at h3
  norm_num at h3

/-- Elementary bridge: on natural casts, `χ` is `raceKernel` (the integrand of
`raceSum`), connecting the analytic layer to `raceSum`. -/
lemma χ_natCast_eq_kernel (n : ℕ) : χ (n : ZMod 4) = ((raceKernel n : ℤ) : ℂ) := by
  unfold χ raceKernel
  rw [MulChar.ringHomComp_apply, ZMod.χ₄_nat_eq_if_mod_four]
  have h4 : n % 4 = 0 ∨ n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
  have h2 : n % 2 = n % 4 % 2 := by omega
  rcases h4 with h | h | h | h <;> rw [h2, h] <;> norm_num

/-- Elementary bridge, literal `if`-chain form (matching `raceSum`'s integrand). -/
lemma χ_natCast_eq_ite (n : ℕ) :
    χ (n : ZMod 4) = ((if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0 : ℤ) : ℂ) := by
  rw [χ_natCast_eq_kernel]
  rfl

/-- Value lemma: `χ = 1` on `1 mod 4`. -/
lemma χ_natCast_one_mod_four {n : ℕ} (h : n % 4 = 1) : χ (n : ZMod 4) = 1 := by
  unfold χ
  rw [MulChar.ringHomComp_apply, ZMod.χ₄_nat_one_mod_four h]
  norm_num

/-- Value lemma: `χ = -1` on `3 mod 4`. -/
lemma χ_natCast_three_mod_four {n : ℕ} (h : n % 4 = 3) : χ (n : ZMod 4) = -1 := by
  unfold χ
  rw [MulChar.ringHomComp_apply, ZMod.χ₄_nat_three_mod_four h]
  norm_num

/-- Value lemma: `χ = 0` on even numbers. -/
lemma χ_natCast_even {n : ℕ} (h : n % 2 = 0) : χ (n : ZMod 4) = 0 := by
  unfold χ
  rw [MulChar.ringHomComp_apply, ZMod.χ₄_nat_eq_if_mod_four, if_pos h]
  norm_num

/-- `‖χ n‖ ≤ 1`. -/
lemma norm_χ_le_one (a : ZMod 4) : ‖χ a‖ ≤ 1 := χ.norm_le_one a

/-- `χ(p)² = 1` at odd primes, `0` at `2` — identifies the `k = 2` layer with `layerB`
(see `tsum_term_two_eq_layerB`). -/
lemma χ_sq_eq_ite (p : Nat.Primes) :
    χ ((p : ℕ) : ZMod 4) ^ 2 = if (p : ℕ) = 2 then 0 else 1 := by
  by_cases hp2 : (p : ℕ) = 2
  · rw [if_pos hp2, χ_natCast_even (by omega)]
    ring
  · rw [if_neg hp2]
    rcases p.prop.eq_two_or_odd with h | h
    · exact absurd h hp2
    have h4 : (p : ℕ) % 4 = 1 ∨ (p : ℕ) % 4 = 3 := by omega
    rcases h4 with h4 | h4
    · rw [χ_natCast_one_mod_four h4]; ring
    · rw [χ_natCast_three_mod_four h4]; ring

/-! ## Norm estimates for the Euler factors -/

/-- `‖χ(p) p^(-s)‖ ≤ p^(-Re s)` (the `norm_natCast_cpow` identity + `‖χ‖ ≤ 1`). -/
lemma norm_χ_mul_cpow_le (p : Nat.Primes) (s : ℂ) :
    ‖χ ((p : ℕ) : ZMod 4) * ((p : ℕ) : ℂ) ^ (-s)‖ ≤ ((p : ℕ) : ℝ) ^ (-s.re) := by
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos p.prop.pos, Complex.neg_re]
  calc ‖χ ((p : ℕ) : ZMod 4)‖ * ((p : ℕ) : ℝ) ^ (-s.re)
      ≤ 1 * ((p : ℕ) : ℝ) ^ (-s.re) := by
        apply mul_le_mul_of_nonneg_right (norm_χ_le_one _)
        positivity
    _ = ((p : ℕ) : ℝ) ^ (-s.re) := one_mul _

/-- Base monotonicity: `p^(-σ) ≤ 2^(-σ)` for `σ ≥ 0`. -/
lemma rpow_neg_le_two_rpow_neg (p : Nat.Primes) {σ : ℝ} (hσ : 0 ≤ σ) :
    ((p : ℕ) : ℝ) ^ (-σ) ≤ (2 : ℝ) ^ (-σ) := by
  have h2p : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.prop.two_le
  exact Real.rpow_le_rpow_of_nonpos two_pos h2p (by linarith)

/-- `2^(-1/2) ≤ 3/4`: the crude constant behind the geometric-tail bound for `layerT`. -/
lemma two_rpow_neg_half_le : (2 : ℝ) ^ (-(1 / 2) : ℝ) ≤ 3 / 4 := by
  have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg (by norm_num) _
  have h1 : ((2 : ℝ) ^ (-(1 / 2) : ℝ)) ^ (2 : ℕ) = 1 / 2 := by
    rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(1 / 2) : ℝ)) 2, ← Real.rpow_mul (by norm_num)]
    have he : (-(1 / 2) : ℝ) * ((2 : ℕ) : ℝ) = -1 := by norm_num
    rw [he, Real.rpow_neg_one]
    norm_num
  nlinarith [h0, h1, sq_nonneg ((2 : ℝ) ^ (-(1 / 2) : ℝ) - 3 / 4)]

/-- `‖χ(p) p^(-s)‖ ≤ 3/4` on `Re s ≥ 1/2` (the geometric-tail bound for `layerT`). -/
lemma norm_χ_mul_cpow_le_three_quarters (p : Nat.Primes) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖χ ((p : ℕ) : ZMod 4) * ((p : ℕ) : ℂ) ^ (-s)‖ ≤ 3 / 4 := by
  refine (norm_χ_mul_cpow_le p s).trans ?_
  refine ((rpow_neg_le_two_rpow_neg p (by linarith)).trans ?_)
  exact (Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)).trans two_rpow_neg_half_le

/-- `‖χ(p) p^(-s)‖ ≤ 1/2` on `Re s ≥ 1` (the domain of the per-prime split). -/
lemma norm_χ_mul_cpow_le_half (p : Nat.Primes) {s : ℂ} (hs : 1 ≤ s.re) :
    ‖χ ((p : ℕ) : ZMod 4) * ((p : ℕ) : ℂ) ^ (-s)‖ ≤ 1 / 2 := by
  refine (norm_χ_mul_cpow_le p s).trans ?_
  have h1 : ((p : ℕ) : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-s.re) :=
    rpow_neg_le_two_rpow_neg p (by linarith)
  have h2 : (2 : ℝ) ^ (-s.re) ≤ (2 : ℝ) ^ (-1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le one_le_two (by linarith)
  have h3 : (2 : ℝ) ^ (-1 : ℝ) = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
  rw [h3] at h2
  exact h1.trans h2

/-- `‖χ(p) p^(-s)‖ ≤ p^(-1/2)` on `Re s ≥ 1/2` (feeds the `p^(-3/2)` bound for `layerT`). -/
lemma norm_χ_mul_cpow_le_rpow_neg_half (p : Nat.Primes) {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖χ ((p : ℕ) : ZMod 4) * ((p : ℕ) : ℂ) ^ (-s)‖ ≤ ((p : ℕ) : ℝ) ^ (-(1 / 2) : ℝ) := by
  refine (norm_χ_mul_cpow_le p s).trans ?_
  refine Real.rpow_le_rpow_of_exponent_le ?_ (by linarith)
  exact_mod_cast p.prop.one_lt.le

/-- `(-(2*s)).re = -(2*s.re)` casting helper. -/
lemma neg_two_mul_re (s : ℂ) : (-(2 * s)).re = -(2 * s.re) := by
  simp [Complex.mul_re]

/-! ## The Euler-product layers -/

/-- Per-prime `k ≥ 3` tail `t_p(s) = Σ_{k≥0} (χ(p) p^(-s))^(k+3) / (k+3)`.
The compact form `z_p^(k+3)/(k+3)` (rather than the expanded
`χ(p)^(k+3) p^(-(k+3)s)/(k+3)`) is chosen so that the tail produced by peeling three
terms off `hasSum_neg_log_one_sub` is *definitionally* `tp p s` (see `neg_log_split`). -/
noncomputable def tp (p : Nat.Primes) (s : ℂ) : ℂ :=
  ∑' k : ℕ, (χ ((p : ℕ) : ZMod 4) * ((p : ℕ) : ℂ) ^ (-s)) ^ (k + 3) / ((k + 3 : ℕ) : ℂ)

/-- The `k ≥ 3` layer `T(s) = Σ_p t_p(s)`. -/
noncomputable def layerT (s : ℂ) : ℂ := ∑' p : Nat.Primes, tp p s

/-- The `k = 2` layer `B(s) = (1/2) Σ_{p odd} p^(-2s)`, with an `if`-mask at
`p = 2` (`χ(2)² = 0`, `χ(p)² = 1` for odd `p`; see `χ_sq_eq_ite`,
`tsum_term_two_eq_layerB`).  Exponent convention: `-(2 * s)`. -/
noncomputable def layerB (s : ℂ) : ℂ :=
  (1 / 2) * ∑' p : Nat.Primes, if (p : ℕ) = 2 then 0 else ((p : ℕ) : ℂ) ^ (-(2 * s))

/-- Real companion of `layerB` (real `rpow`; agreement: `layerB_ofReal`). -/
noncomputable def layerBReal (σ : ℝ) : ℝ :=
  (1 / 2) * ∑' p : Nat.Primes, if (p : ℕ) = 2 then 0 else ((p : ℕ) : ℝ) ^ (-(2 * σ))

/-- Real companion of `tp` (agreement: `tp_ofReal`). -/
noncomputable def tpReal (p : Nat.Primes) (σ : ℝ) : ℝ :=
  ∑' k : ℕ, ((raceKernel (p : ℕ) : ℝ) * ((p : ℕ) : ℝ) ^ (-σ)) ^ (k + 3) / ((k + 3 : ℕ) : ℝ)

/-- Real companion of `layerT` (agreement: `layerT_ofReal`). -/
noncomputable def layerTReal (σ : ℝ) : ℝ := ∑' p : Nat.Primes, tpReal p σ

/-- Explicit bound for `layerB` on real `s ≥ 1`: `cB = (1/2) Σ_p p^(-2)`
(finite by `Nat.Primes.summable_rpow`). -/
noncomputable def cB : ℝ := (1 / 2) * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ)

/-- Explicit uniform bound for `layerT` on `Re s ≥ 1/2`:
`cT = (4/3) Σ_p p^(-3/2)` (a crude `κ ≤ 4` version of the `κ/3 · Σ n^(-3/2)` bound). -/
noncomputable def cT : ℝ := (4 / 3) * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ)

end A362583
