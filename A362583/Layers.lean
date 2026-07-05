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
# Layer infrastructure for Step D (divergence transfer, log series, the B/T layers)

Proof-layer declarations for the analytic Step D:

* `A362583.χ` — the project Dirichlet character mod 4, with value lemmas and the
  elementary bridge `χ_natCast_eq_kernel` / `χ_natCast_eq_ite` to `raceSum`'s
  integrand (`raceKernel`).
* Divergence transfer: `exists_one_lt_tsum_primes_rpow_gt` (`P(s) = Σ_p p^(-s)`
  blows up as `s ↓ 1`) and `exists_layerBReal_gt` (`layerBReal` blows up as
  `s ↓ 1/2`).  Only prime input anywhere: the divergence of `Σ 1/p`
  (`Nat.Primes.not_summable_one_div`).
* The logarithm series: `hasSum_neg_log_one_sub`, `neg_log_one_sub_eq_tsum`.
* The `B` and `T` layers `layerB`, `layerT` (real companions `layerBReal`,
  `layerTReal`), summability, holomorphy on `Ω = {1/2 < re}`, explicit bounds
  `C_B`, `C_T`, positivity, and real-axis agreement lemmas (`layerB_ofReal` etc.).
* Preparation for the Euler wiring: the per-prime split `neg_log_split`, the `layerB`
  identification `tsum_term_two_eq_layerB`, and the three absolute-summability facts
  `summable_norm_term_one`, `summable_norm_term_two`, `summable_norm_tp`.
-/

namespace A362583

open Complex

/-! ## The race kernel and the character χ -/

/-- The integrand of `raceSum`, named: `+1` on `1 mod 4`, `-1` on `3 mod 4`, `0` else. -/
def raceKernel (n : ℕ) : ℤ := if n % 4 = 1 then 1 else if n % 4 = 3 then -1 else 0

/-- `raceSum` is the sum of `raceKernel` over primes `≤ N` (definitional). -/
lemma raceSum_eq_sum_raceKernel (N : ℕ) :
    raceSum N = ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, raceKernel p := rfl

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

/-! ## The layers `B` and `T` -/

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

/-- Explicit bound for `layerB` on real `s ≥ 1`: `C_B = (1/2) Σ_p p^(-2)`
(finite by `Nat.Primes.summable_rpow`). -/
noncomputable def C_B : ℝ := (1 / 2) * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ)

/-- Explicit uniform bound for `layerT` on `Re s ≥ 1/2`:
`C_T = (4/3) Σ_p p^(-3/2)` (a crude `κ ≤ 4` version of the `κ/3 · Σ n^(-3/2)` bound). -/
noncomputable def C_T : ℝ := (4 / 3) * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ)

/-! ## Divergence transfer (the sole use of the divergence of Σ 1/p) -/

/-- Step 1: a nonneg non-summable family has unbounded finite subsums. -/
private lemma exists_finset_gt_of_not_summable {f : Nat.Primes → ℝ} (h0 : ∀ p, 0 ≤ f p)
    (hns : ¬ Summable f) (M : ℝ) : ∃ F : Finset Nat.Primes, M < ∑ p ∈ F, f p := by
  by_contra hcon
  exact hns (summable_of_sum_le (Pi.le_def.mpr h0)
    (fun F ↦ not_lt.mp fun hF ↦ hcon ⟨F, hF⟩))

/-- Step 1': `Σ 1/p` over odd primes is still non-summable (drop the `p = 2` term). -/
private lemma not_summable_one_div_odd :
    ¬ Summable (fun p : Nat.Primes ↦ if (p : ℕ) = 2 then 0 else 1 / ((p : ℕ) : ℝ)) := by
  intro hg
  have htwo : Summable (fun p : Nat.Primes ↦ if (p : ℕ) = 2 then 1 / ((p : ℕ) : ℝ) else 0) := by
    refine summable_of_ne_finset_zero (s := {(⟨2, Nat.prime_two⟩ : Nat.Primes)}) ?_
    intro p hp
    rw [if_neg]
    intro hp2
    exact hp (Finset.mem_singleton.mpr (Subtype.ext hp2))
  have h1 : Summable (fun p : Nat.Primes ↦ 1 / ((p : ℕ) : ℝ)) := by
    refine (hg.add htwo).congr fun p ↦ ?_
    by_cases hp : (p : ℕ) = 2 <;> simp [hp]
  exact Nat.Primes.not_summable_one_div h1

/-- Step 1'' packaged: finite sets of *odd* primes with `Σ 1/p > M` exist for every
`M` (feeds the `layerBReal` blow-up; `Σ_{p odd} 1/p = Σ_p 1/p − 1/2`). -/
private lemma exists_odd_finset_one_div_gt (M : ℝ) :
    ∃ F : Finset Nat.Primes, (∀ p ∈ F, (p : ℕ) ≠ 2) ∧ M < ∑ p ∈ F, 1 / ((p : ℕ) : ℝ) := by
  obtain ⟨F, hF⟩ := exists_finset_gt_of_not_summable
    (fun p ↦ by
      rcases eq_or_ne (p : ℕ) 2 with h | h
      · simp [h]
      · simp only [if_neg h]
        positivity)
    not_summable_one_div_odd M
  refine ⟨F.filter (fun p : Nat.Primes ↦ ¬ (p : ℕ) = 2),
    fun p hp ↦ (Finset.mem_filter.mp hp).2, ?_⟩
  have heq : ∑ p ∈ F.filter (fun p : Nat.Primes ↦ ¬ (p : ℕ) = 2), 1 / ((p : ℕ) : ℝ)
      = ∑ p ∈ F, if (p : ℕ) = 2 then 0 else 1 / ((p : ℕ) : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rcases eq_or_ne (p : ℕ) 2 with hp | hp
    · rw [if_neg (not_not_intro hp), if_pos hp]
    · rw [if_pos hp, if_neg hp]
  rw [heq]
  exact hF

/-- Step 2 (continuity padding): a finite rpow sum exceeding `M` at `u₀` still
exceeds `M` slightly to the right of `u₀`. -/
private lemma exists_right_of_sum_rpow_gt {F : Finset Nat.Primes} {a u₀ M : ℝ}
    (hM : M < ∑ p ∈ F, ((p : ℕ) : ℝ) ^ (-(a * u₀))) {η : ℝ} (hη : 0 < η) :
    ∃ u : ℝ, u₀ < u ∧ u < u₀ + η ∧ M < ∑ p ∈ F, ((p : ℕ) : ℝ) ^ (-(a * u)) := by
  have hcont : Continuous (fun u : ℝ ↦ ∑ p ∈ F, ((p : ℕ) : ℝ) ^ (-(a * u))) := by
    refine continuous_finsetSum F fun p _ ↦ ?_
    have hrw : (fun u : ℝ ↦ ((p : ℕ) : ℝ) ^ (-(a * u)))
        = fun u ↦ Real.exp (Real.log ((p : ℕ) : ℝ) * (-(a * u))) := by
      funext u
      rw [Real.rpow_def_of_pos (by exact_mod_cast p.prop.pos)]
    rw [hrw]
    fun_prop
  have hopen : IsOpen {u : ℝ | M < ∑ p ∈ F, ((p : ℕ) : ℝ) ^ (-(a * u))} :=
    isOpen_lt continuous_const hcont
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen u₀ hM
  have hmin : 0 < min ε η := lt_min hε hη
  refine ⟨u₀ + min ε η / 2, by linarith, by linarith [min_le_right ε η], ?_⟩
  have hmem : u₀ + min ε η / 2 ∈ Metric.ball u₀ ε := by
    rw [Metric.mem_ball, Real.dist_eq, show u₀ + min ε η / 2 - u₀ = min ε η / 2 by ring,
      abs_of_pos (by linarith)]
    linarith [min_le_left ε η]
  exact hball hmem

/-- **Divergence transfer at `s ↓ 1`**: for every `M` and `η > 0` there is a
real `σ ∈ (1, 1+η)` with `P(σ) = Σ_p p^(-σ) > M`.  Only prime input: the
divergence of `Σ 1/p`. -/
theorem exists_one_lt_tsum_primes_rpow_gt (M : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ σ : ℝ, 1 < σ ∧ σ < 1 + η ∧ M < ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ) := by
  obtain ⟨F, hF⟩ := exists_finset_gt_of_not_summable (fun p ↦ by positivity)
    Nat.Primes.not_summable_one_div M
  have hF1 : M < ∑ p ∈ F, ((p : ℕ) : ℝ) ^ (-(1 * (1 : ℝ))) := by
    refine hF.trans_le (le_of_eq (Finset.sum_congr rfl fun p _ ↦ ?_))
    rw [show -(1 * (1 : ℝ)) = -1 by norm_num, Real.rpow_neg_one, one_div]
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_right_of_sum_rpow_gt hF1 hη
  have hsum : Summable (fun p : Nat.Primes ↦ ((p : ℕ) : ℝ) ^ (-u)) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  refine ⟨u, hu1, hu2, lt_of_lt_of_le ?_ (hsum.sum_le_tsum F fun p _ ↦ by positivity)⟩
  refine lt_of_lt_of_le hu3 (le_of_eq (Finset.sum_congr rfl fun p _ ↦ ?_))
  rw [one_mul]

/-- Summability of the real `layerB` integrand for `σ > 1/2`. -/
lemma summable_layerBReal_term {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun p : Nat.Primes ↦ if (p : ℕ) = 2 then 0 else ((p : ℕ) : ℝ) ^ (-(2 * σ))) := by
  refine Summable.of_nonneg_of_le (fun p ↦ ?_) (fun p ↦ ?_)
    (Nat.Primes.summable_rpow.mpr (by linarith : -(2 * σ) < -1))
  · rcases eq_or_ne (p : ℕ) 2 with h | h
    · simp [h]
    · simp only [if_neg h]
      positivity
  · rcases eq_or_ne (p : ℕ) 2 with h | h
    · simp only [if_pos h]
      positivity
    · simp [h]

/-- **Divergence transfer at `s ↓ 1/2` (`layerBReal` blow-up)**: for every `M` and
`η > 0` there is a real `σ ∈ (1/2, 1/2+η)` with `layerBReal σ > M`.  Only prime
input: the divergence of `Σ 1/p`. -/
theorem exists_layerBReal_gt (M : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 / 2 + η ∧ M < layerBReal σ := by
  obtain ⟨F, hFodd, hF⟩ := exists_odd_finset_one_div_gt (2 * M)
  have hF1 : 2 * M < ∑ p ∈ F, ((p : ℕ) : ℝ) ^ (-(2 * (1 / 2 : ℝ))) := by
    refine hF.trans_le (le_of_eq (Finset.sum_congr rfl fun p _ ↦ ?_))
    rw [show -(2 * (1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one, one_div]
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_right_of_sum_rpow_gt hF1 hη
  have hsum := summable_layerBReal_term (σ := u) hu1
  have hle : ∑ p ∈ F, ((p : ℕ) : ℝ) ^ (-(2 * u))
      ≤ ∑' p : Nat.Primes, if (p : ℕ) = 2 then 0 else ((p : ℕ) : ℝ) ^ (-(2 * u)) := by
    have heq : ∑ p ∈ F, ((p : ℕ) : ℝ) ^ (-(2 * u))
        = ∑ p ∈ F, if (p : ℕ) = 2 then 0 else ((p : ℕ) : ℝ) ^ (-(2 * u)) :=
      Finset.sum_congr rfl fun p hp ↦ (if_neg (hFodd p hp)).symm
    rw [heq]
    exact hsum.sum_le_tsum F fun p _ ↦ by
      rcases eq_or_ne (p : ℕ) 2 with h | h
      · simp [h]
      · simp only [if_neg h]
        positivity
  refine ⟨u, hu1, hu2, ?_⟩
  unfold layerBReal
  linarith

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

/-- **Uniform bound for `T`**: `‖T(s)‖ ≤ C_T` on `Re s ≥ 1/2`. -/
theorem norm_layerT_le {s : ℂ} (hs : 1 / 2 ≤ s.re) : ‖layerT s‖ ≤ C_T := by
  unfold layerT C_T
  calc ‖∑' p : Nat.Primes, tp p s‖ ≤ ∑' p : Nat.Primes, ‖tp p s‖ :=
        norm_tsum_le_tsum_norm (summable_norm_tp hs)
    _ ≤ ∑' p : Nat.Primes, 4 / 3 * ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) := by
        refine (summable_norm_tp hs).tsum_le_tsum (fun p ↦ norm_tp_le p hs) ?_
        exact (Nat.Primes.summable_rpow.mpr (by norm_num)).mul_left (4 / 3)
    _ = 4 / 3 * ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) := tsum_mul_left

/-- `C_B ≥ 0`. -/
lemma C_B_nonneg : 0 ≤ C_B := by
  unfold C_B
  have h : 0 ≤ ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-2 : ℝ) :=
    tsum_nonneg fun p ↦ by positivity
  linarith

/-- `C_T ≥ 0`. -/
lemma C_T_nonneg : 0 ≤ C_T := by
  unfold C_T
  have h : 0 ≤ ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-(3 / 2) : ℝ) :=
    tsum_nonneg fun p ↦ by positivity
  linarith

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

/-- **Bound for `layerBReal`**: `layerBReal σ ≤ C_B` for real `σ ≥ 1`. -/
theorem layerBReal_le_C_B {σ : ℝ} (hσ : 1 ≤ σ) : layerBReal σ ≤ C_B := by
  unfold layerBReal C_B
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

/-- `0 ≤ Re (layerB σ)` for real `σ`. -/
lemma layerB_re_nonneg (σ : ℝ) : 0 ≤ (layerB (σ : ℂ)).re := by
  rw [layerB_re]; exact layerBReal_nonneg σ

/-- `layerT` is real on the real axis. -/
lemma layerT_im (σ : ℝ) : (layerT (σ : ℂ)).im = 0 := by
  rw [layerT_ofReal]; exact Complex.ofReal_im _

/-- Real part of `layerT` on the real axis. -/
lemma layerT_re (σ : ℝ) : (layerT (σ : ℂ)).re = layerTReal σ := by
  rw [layerT_ofReal]; exact Complex.ofReal_re _

/-- `‖layerB σ‖ ≤ C_B` for real `σ ≥ 1`. -/
theorem norm_layerB_le {σ : ℝ} (hσ : 1 ≤ σ) : ‖layerB (σ : ℂ)‖ ≤ C_B := by
  rw [layerB_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (layerBReal_nonneg σ)]
  exact layerBReal_le_C_B hσ

/-- Real-companion bound `|layerTReal σ| ≤ C_T` for real `σ ≥ 1/2`. -/
lemma abs_layerTReal_le {σ : ℝ} (hσ : 1 / 2 ≤ σ) : |layerTReal σ| ≤ C_T := by
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
