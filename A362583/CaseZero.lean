/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
import A362583.CaseNonzero
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.IntervalCases

/-!
# Case `c = 0` endgame: the race sum is never linear (Step D)

The main analytic theorem `raceSum_not_linear`: there are no constants `c`, `C` with
`|S(N) - c·π(N)| ≤ C` for all `N`, where `S = raceSum` and `π = Nat.primeCounting`.

`c_eq_zero_of_raceSum_linear` (`A362583/CaseNonzero.lean`) forces `c = 0`, reducing to the
bounded-race hypothesis `|S(N)| ≤ C`.  Then:

* **Bounded partial sums.** The partial sums of `fChi` are exactly the race sums
  (`sum_range_fChi`), hence bounded by `C` in norm (`norm_sum_range_fChi_le`), and they
  vanish below `n = 2` (`sum_range_fChi_vanish`).  Consequently the by-parts series
  `bpSeries fChi` (`A362583/BoundedHolo.lean`) is holomorphic on `{Re s > 0}`, satisfies
  `‖bpSeries fChi σ‖ ≤ C` for real `σ ≥ 0`, and agrees with `layerA` on `{Re s > 1}`.
* **The continued logarithm.** `contLog := bpSeries fChi + layerB + layerT` is holomorphic
  on `Ω = {Re s > 1/2}` (`differentiableOn_contLog`) and `exp (contLog s) = L(χ, s)` on
  `{Re s > 1}` (`exp_contLog_eq`, via the Euler wiring `exp_layers_eq_LFunction`).
* **Identity theorem.** By the identity theorem on the open preconnected `Ω`,
  `exp ∘ contLog = L(χ, ·)` on all of `Ω` (`exp_contLog_eqOn`).
* **Endgame at `1/2` (single-point form).** `L(χ, ·)` is entire, hence continuous at `1/2`
  with some bound `M₀` on a `δ₀`-ball.  The divergence transfer `exists_layerBReal_gt`
  supplies a real `σ ∈ (1/2, 1/2 + δ₀)` with `layerBReal σ > log M₀ + C + C_T`; at
  `s* = σ` the identity gives `‖L(χ, σ)‖ = exp (Re (contLog σ)) > M₀`, contradicting the
  ball bound.  The contradiction is evaluated at a single point, with no filters toward
  `1/2⁺`.
-/

namespace A362583

open Complex Filter Topology

/-! ## Bounded partial sums of `fChi` and their consequences -/

/-- Side condition: the partial sums of `fChi` vanish below `n₀ = 2`
(`fChi 0 = fChi 1 = 0`; feeds `norm_bpSeries_le_const`). -/
lemma sum_range_fChi_vanish : ∀ n < 2, ∑ k ∈ Finset.range (n + 1), fChi k = 0 := by
  intro n hn
  interval_cases n <;> simp [Finset.sum_range_succ, fChi_zero, fChi_one]

/-- Under the bounded-race hypothesis `|S(N)| ≤ C`, the partial sums of `fChi` are
bounded by `C` in norm — they are exactly the race sums (`sum_range_fChi`). -/
lemma norm_sum_range_fChi_le {C : ℝ} (hS : ∀ N : ℕ, |(raceSum N : ℝ)| ≤ C) (n : ℕ) :
    ‖∑ k ∈ Finset.range (n + 1), fChi k‖ ≤ C := by
  rw [sum_range_fChi, ← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
  exact hS n

/-! ## The continued logarithm `G = Ã + B + T` on `Ω = {Re s > 1/2}` -/

/-- The continued logarithm `G := Ã + B + T`, where `Ã = bpSeries fChi`
is the by-parts continuation of the `k = 1` layer and `B`, `T` are the `k = 2` and `k ≥ 3`
layers.  Under the bounded-race hypothesis it is holomorphic on `Ω = {Re s > 1/2}`
(`differentiableOn_contLog`) and `exp ∘ contLog = L(χ, ·)` there (`exp_contLog_eqOn`). -/
noncomputable def contLog (s : ℂ) : ℂ := bpSeries fChi s + layerB s + layerT s

/-- Holomorphy: under the bounded-race hypothesis, `contLog` is holomorphic on
`Ω = {Re s > 1/2}` (holomorphy of `bpSeries fChi`, `layerB`, and `layerT`). -/
lemma differentiableOn_contLog {C : ℝ}
    (hB : ∀ n, ‖∑ k ∈ Finset.range (n + 1), fChi k‖ ≤ C) :
    DifferentiableOn ℂ contLog {s : ℂ | 1 / 2 < s.re} := by
  unfold contLog
  have h1 : DifferentiableOn ℂ (bpSeries fChi) {s : ℂ | 1 / 2 < s.re} := by
    refine (differentiableOn_bpSeries hB).mono fun s hs ↦ ?_
    simp only [Set.mem_setOf_eq] at hs ⊢
    linarith
  exact (h1.add differentiableOn_layerB).add differentiableOn_layerT

/-- Identification on `{Re s > 1}`: `exp (contLog s) = L(χ, s)` for `Re s > 1` —
the by-parts series agrees with `layerA` there (`tsum_mul_cpow_neg_eq_bpSeries` +
`layerA_eq_tsum_fChi`), and the Euler wiring `exp_layers_eq_LFunction`
applies. -/
lemma exp_contLog_eq {C : ℝ} (hB : ∀ n, ‖∑ k ∈ Finset.range (n + 1), fChi k‖ ≤ C)
    {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (contLog s) = DirichletCharacter.LFunction χ s := by
  have hA : bpSeries fChi s = layerA s := by
    rw [layerA_eq_tsum_fChi, tsum_mul_cpow_neg_eq_bpSeries hB hs]
  unfold contLog
  rw [hA]
  exact exp_layers_eq_LFunction hs

/-! ## The identity theorem on `Ω` -/

/-- **Identity theorem**: under the bounded-race hypothesis,
`exp ∘ contLog = L(χ, ·)` on all of `Ω = {Re s > 1/2}` — `Ω` is open and preconnected,
both sides are holomorphic on `Ω` and agree on the open `{Re s > 1} ∋ 2`. -/
lemma exp_contLog_eqOn {C : ℝ} (hB : ∀ n, ‖∑ k ∈ Finset.range (n + 1), fChi k‖ ≤ C) :
    Set.EqOn (fun s ↦ Complex.exp (contLog s)) (DirichletCharacter.LFunction χ)
      {s : ℂ | 1 / 2 < s.re} := by
  have hf : DifferentiableOn ℂ (fun s ↦ Complex.exp (contLog s)) {s : ℂ | 1 / 2 < s.re} :=
    (differentiableOn_contLog hB).cexp
  have hg : DifferentiableOn ℂ (DirichletCharacter.LFunction χ) {s : ℂ | 1 / 2 < s.re} :=
    (DirichletCharacter.differentiable_LFunction χ_ne_one).differentiableOn
  have hfg : Set.EqOn (fun s ↦ Complex.exp (contLog s)) (DirichletCharacter.LFunction χ)
      {s : ℂ | 1 < s.re} := fun s hs ↦ exp_contLog_eq hB hs
  have hΩ : IsOpen {s : ℂ | 1 / 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hO : IsOpen {s : ℂ | 1 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hpre : IsPreconnected {s : ℂ | 1 / 2 < s.re} :=
    (convex_halfSpace_re_gt (1 / 2 : ℝ)).isPreconnected
  have h₂O : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by
    norm_num [Set.mem_setOf_eq]
  have h₂Ω : (2 : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by
    norm_num [Set.mem_setOf_eq]
  have hev : (fun s ↦ Complex.exp (contLog s)) =ᶠ[𝓝 (2 : ℂ)]
      DirichletCharacter.LFunction χ :=
    Filter.eventuallyEq_of_mem (hO.mem_nhds h₂O) hfg
  exact (hf.analyticOnNhd hΩ).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd hΩ) hpre h₂Ω hev

/-! ## The endgame at `1/2` (single-point form) -/

/-- **Main analytic theorem**: the mod-4 prime race is never linear — there are no
constants `c`, `C` with `|S(N) - c·π(N)| ≤ C` for all `N`, where `S = raceSum` and
`π = Nat.primeCounting` (# primes `≤ N`).

Case `c ≠ 0` is `c_eq_zero_of_raceSum_linear`; case `c = 0` runs the Step D endgame: the
continued logarithm `contLog` satisfies `exp ∘ contLog = L(χ, ·)` on `Ω = {Re s > 1/2}`
by the identity theorem, but `Re (contLog σ) ≥ layerBReal σ - C - C_T → ∞` as `σ ↓ 1/2`
by divergence transfer, contradicting the continuity of the entire `L(χ, ·)` at `1/2` —
evaluated at a single point `σ*`, with no filters. -/
theorem raceSum_not_linear :
    ¬ ∃ (c C : ℝ), ∀ N : ℕ, |(raceSum N : ℝ) - c * (Nat.primeCounting N : ℝ)| ≤ C := by
  rintro ⟨c, C, hC⟩
  -- Case `c ≠ 0` (CaseNonzero.lean) forces `c = 0`.
  have hc : c = 0 := c_eq_zero_of_raceSum_linear hC
  subst hc
  have hS : ∀ N : ℕ, |(raceSum N : ℝ)| ≤ C := fun N ↦ by simpa using hC N
  -- Bounded partial sums, and the half-plane identity.
  have hB : ∀ n, ‖∑ k ∈ Finset.range (n + 1), fChi k‖ ≤ C := norm_sum_range_fChi_le hS
  have hEq := exp_contLog_eqOn hB
  -- `L(χ, ·)` is entire, hence continuous at `1/2`: a bound `M₀` on a `δ₀`-ball.
  obtain ⟨M₀, hM₀pos, δ₀, hδ₀pos, hball⟩ :
      ∃ M₀ : ℝ, 0 < M₀ ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ s : ℂ, ‖s - ((1 / 2 : ℝ) : ℂ)‖ < δ₀ →
        ‖DirichletCharacter.LFunction χ s‖ < M₀ := by
    have hcont : ContinuousAt (DirichletCharacter.LFunction χ) ((1 / 2 : ℝ) : ℂ) :=
      (DirichletCharacter.differentiable_LFunction χ_ne_one).continuous.continuousAt
    obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := Metric.continuousAt_iff.mp hcont 1 one_pos
    refine ⟨‖DirichletCharacter.LFunction χ ((1 / 2 : ℝ) : ℂ)‖ + 1,
      add_pos_of_nonneg_of_pos (norm_nonneg _) one_pos, δ₀, hδ₀pos, fun s hs ↦ ?_⟩
    have hd : dist (DirichletCharacter.LFunction χ s)
        (DirichletCharacter.LFunction χ ((1 / 2 : ℝ) : ℂ)) < 1 :=
      hδ₀ (by rwa [dist_eq_norm])
    rw [dist_eq_norm] at hd
    have hn := norm_sub_norm_le (DirichletCharacter.LFunction χ s)
      (DirichletCharacter.LFunction χ ((1 / 2 : ℝ) : ℂ))
    linarith
  -- Divergence transfer: a single point `σ ∈ (1/2, 1/2 + δ₀)` where `layerBReal` is huge.
  obtain ⟨σ, hσlo, hσhi, hσB⟩ :=
    exists_layerBReal_gt (Real.log M₀ + C + C_T) hδ₀pos
  -- `s* := σ` lies in `Ω`; evaluate the identity there.
  have hmem : ((σ : ℝ) : ℂ) ∈ {s : ℂ | 1 / 2 < s.re} := by
    simp only [Set.mem_setOf_eq, Complex.ofReal_re]
    exact hσlo
  have hexp : Complex.exp (contLog ((σ : ℝ) : ℂ)) = DirichletCharacter.LFunction χ σ :=
    hEq hmem
  have hnormL : ‖DirichletCharacter.LFunction χ ((σ : ℝ) : ℂ)‖ =
      Real.exp ((contLog ((σ : ℝ) : ℂ)).re) := by
    rw [← hexp, Complex.norm_exp]
  -- `Re (contLog σ) = Re (bpSeries fChi σ) + layerBReal σ + layerTReal σ`.
  have hre : (contLog ((σ : ℝ) : ℂ)).re =
      (bpSeries fChi ((σ : ℝ) : ℂ)).re + layerBReal σ + layerTReal σ := by
    simp only [contLog, Complex.add_re, layerB_re, layerT_re]
  -- Lower bounds: `Re (bpSeries fChi σ) ≥ -C` and `layerTReal σ ≥ -C_T`.
  have hσ0 : (0 : ℝ) ≤ σ := by linarith
  have hbp : ‖bpSeries fChi ((σ : ℝ) : ℂ)‖ ≤ C :=
    norm_bpSeries_le_const (n₀ := 2) hB one_le_two sum_range_fChi_vanish hσ0
  have hbpre : -C ≤ (bpSeries fChi ((σ : ℝ) : ℂ)).re :=
    (abs_le.mp ((Complex.abs_re_le_norm _).trans hbp)).1
  have hT : -C_T ≤ layerTReal σ := (abs_le.mp (abs_layerTReal_le hσlo.le)).1
  -- `Re (contLog σ) > log M₀`, so `‖L(χ, σ)‖ > M₀` …
  have hGgt : Real.log M₀ < (contLog ((σ : ℝ) : ℂ)).re := by
    rw [hre]
    linarith
  have hLbig : M₀ < ‖DirichletCharacter.LFunction χ ((σ : ℝ) : ℂ)‖ := by
    rw [hnormL]
    calc M₀ = Real.exp (Real.log M₀) := (Real.exp_log hM₀pos).symm
      _ < Real.exp ((contLog ((σ : ℝ) : ℂ)).re) := Real.exp_lt_exp.mpr hGgt
  -- … but `σ` is within `δ₀` of `1/2`, so `‖L(χ, σ)‖ < M₀`.  Contradiction.
  have hLsmall : ‖DirichletCharacter.LFunction χ ((σ : ℝ) : ℂ)‖ < M₀ := by
    refine hball _ ?_
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith)]
    linarith
  linarith

end A362583
