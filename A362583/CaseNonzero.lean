/-
Copyright (c) 2026 Eric Vergo. Dedicated to the public domain.
Released under CC0 1.0 Universal as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.PrimeCounting
import A362583.BoundedHolo
import A362583.EulerLog

/-!
# Case `c ≠ 0` of Step D (PROOF.md "Case c ≠ 0", steps 1–3)

If the race sum were linear, `|S(N) - c·π(N)| ≤ C` for all `N`, then `c = 0`.  This is the
first half of PROOF.md's consolidated Step D; the entry point `c_eq_zero_of_raceSum_linear`
reduces the full non-linearity theorem to the bounded-race case `|S(N)| ≤ C`.

* **Step 1 (Abel bound).**  The coefficients `fSub c n = fChi n - c·1_prime(n)` have partial
  sums `S(n) - c·π(n)`, bounded by `C` and vanishing below `n = 2`; `norm_bpSeries_le_const`
  (`A362583/BoundedHolo.lean`) bounds the by-parts series, which for real `σ > 1` is
  identified with `A(σ) - c·P(σ)` (`bpSeries_fSub_eq`, via `tsum_mul_cpow_neg_eq_bpSeries`,
  `layerA_eq_tsum_fChi`, and the subtype ↔ indicator bridge `tsum_primes_cpow_eq_tsum_ite`).
  Net real form: `|layerAReal σ - c * primeSum σ| ≤ C` on `σ > 1`
  (`abs_layerAReal_sub_mul_primeSum_le`).
* **Step 2 (`A` bounded on `(1, 2]`).**  On real `σ > 1` the Euler wiring
  (`exp_layers_eq_LFunction` + the three `ofReal` lemmas) shows `L(χ, σ)` is the positive
  real number `exp (A(σ) + B(σ) + T(σ))` (`LFunction_ofReal_eq_exp`), so
  `A(σ) = log (Re L(χ, σ)) - B(σ) - T(σ)`.  `Re L(χ, ·)` is continuous and positive on the
  compact `[1, 2]` — positivity at `σ = 1` combines M3 (`LFunction_apply_one_ne_zero`) with
  one-sided limits pinning `Im L = 0` and `Re L ≥ 0` (`LFunction_one_re_pos`) — so its `log`
  is bounded there; with the `B`/`T` bounds this gives `|layerAReal σ| ≤ K` on `(1, 2]`
  (`exists_bound_abs_layerAReal`).
* **Step 3 (conclusion).**  If `c ≠ 0` then steps 1–2 force `P(σ) ≤ (C + K)/|c|` on
  `(1, 2]`, contradicting the single point `σ* ∈ (1, 2)` with `P(σ*)` large supplied by R1
  (`exists_one_lt_tsum_primes_rpow_gt`, the only prime input).

## Main result

* `c_eq_zero_of_raceSum_linear`: `|S(N) - c·π(N)| ≤ C` for all `N` implies `c = 0`.
-/

namespace A362583

open Complex Filter Topology

/-! ## Step 1: the Abel bound (PROOF.md c≠0 step 1) -/

/-- Step 1 coefficients: `fSub c n = fChi n - c·1_prime(n)`, the ℕ-indexed coefficients of
`A(s) - c·P(s)`.  Partial sums: `sum_range_fSub`. -/
noncomputable def fSub (c : ℝ) (n : ℕ) : ℂ :=
  fChi n - (c : ℂ) * (if n.Prime then 1 else 0)

/-- `π(n)` is the number of primes in `Finset.range (n + 1)` (the `count` ↔ `filter`-card
bridge, matching the `Finset.filter` form of `raceSum`). -/
lemma primeCounting_eq_card_filter (n : ℕ) :
    Nat.primeCounting n = ((Finset.range (n + 1)).filter Nat.Prime).card := by
  rw [Nat.primeCounting_eq_primeCounting'_succ]
  exact Nat.count_eq_card_filter_range _ _

/-- Summing the prime indicator over `k ≤ n` counts the primes `≤ n`. -/
lemma sum_range_ite_prime (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), if k.Prime then (1 : ℂ) else 0)
      = (Nat.primeCounting n : ℂ) := by
  rw [primeCounting_eq_card_filter, Finset.sum_boole]

/-- Step 1: the partial sums of `fSub c` are exactly the race deviation `S(n) - c·π(n)`
(as a complex number). -/
lemma sum_range_fSub (c : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), fSub c k
      = (((raceSum n : ℝ) - c * (Nat.primeCounting n : ℝ) : ℝ) : ℂ) := by
  unfold fSub
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_range_fChi, sum_range_ite_prime]
  push_cast
  ring

/-- Step 1: under the linearity hypothesis, the partial sums of `fSub c` are bounded
by `C` in norm. -/
lemma norm_sum_range_fSub_le {c C : ℝ}
    (hC : ∀ N : ℕ, |(raceSum N : ℝ) - c * (Nat.primeCounting N : ℝ)| ≤ C) (n : ℕ) :
    ‖∑ k ∈ Finset.range (n + 1), fSub c k‖ ≤ C := by
  rw [sum_range_fSub, Complex.norm_real, Real.norm_eq_abs]
  exact hC n

/-- Step 1: the partial sums of `fSub c` vanish below `n = 2` (no primes below `2`). -/
lemma sum_range_fSub_eq_zero (c : ℝ) :
    ∀ n < 2, ∑ k ∈ Finset.range (n + 1), fSub c k = 0 := by
  intro n hn
  interval_cases n <;>
    simp [Finset.sum_range_succ, fSub, fChi_zero, fChi_one, Nat.not_prime_zero,
      Nat.not_prime_one]

/-- `‖fChi n‖ ≤ 1` (the race kernel has values in `{-1, 0, 1}`). -/
lemma norm_fChi_le_one (n : ℕ) : ‖fChi n‖ ≤ 1 := by
  unfold fChi raceKernel
  split_ifs <;> simp

/-- Step 1: absolute convergence of the `fChi` Dirichlet series for `Re s > 1`. -/
lemma summable_fChi_mul_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ ↦ fChi n * (n : ℂ) ^ (-s) := by
  refine Summable.of_norm_bounded_eventually_nat (g := fun n : ℕ ↦ (n : ℝ) ^ (-s.re))
    (Real.summable_nat_rpow.2 (by linarith)) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]
  calc ‖fChi n‖ * (n : ℝ) ^ (-s.re)
      ≤ 1 * (n : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right (norm_fChi_le_one n)
          (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = (n : ℝ) ^ (-s.re) := one_mul _

/-- Step 1: absolute convergence of the prime-indicator Dirichlet series for `Re s > 1`. -/
lemma summable_ite_prime_mul_cpow {s : ℂ} (hs : 1 < s.re) :
    Summable fun n : ℕ ↦ (if n.Prime then (1 : ℂ) else 0) * (n : ℂ) ^ (-s) := by
  refine Summable.of_norm_bounded_eventually_nat (g := fun n : ℕ ↦ (n : ℝ) ^ (-s.re))
    (Real.summable_nat_rpow.2 (by linarith)) ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hn, Complex.neg_re]
  have h1 : ‖if n.Prime then (1 : ℂ) else 0‖ ≤ 1 := by split_ifs <;> simp
  calc ‖if n.Prime then (1 : ℂ) else 0‖ * (n : ℝ) ^ (-s.re)
      ≤ 1 * (n : ℝ) ^ (-s.re) :=
        mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ = (n : ℝ) ^ (-s.re) := one_mul _

/-- Step 1: the subtype ↔ indicator bridge for the prime series `P(s)` (same technique as
`layerA_eq_tsum_fChi`; unconditional). -/
lemma tsum_primes_cpow_eq_tsum_ite (s : ℂ) :
    ∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-s)
      = ∑' n : ℕ, (if n.Prime then (1 : ℂ) else 0) * (n : ℂ) ^ (-s) := by
  have h := tsum_subtype {n : ℕ | n.Prime} (fun n : ℕ ↦ (n : ℂ) ^ (-s))
  calc ∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-s)
      = ∑' n : ℕ, Set.indicator {n : ℕ | n.Prime} (fun n : ℕ ↦ (n : ℂ) ^ (-s)) n := h
    _ = ∑' n : ℕ, (if n.Prime then (1 : ℂ) else 0) * (n : ℂ) ^ (-s) := by
        refine tsum_congr fun n ↦ ?_
        rw [Set.indicator_apply]
        simp only [Set.mem_setOf_eq]
        by_cases hn : n.Prime
        · rw [if_pos hn, if_pos hn, one_mul]
        · rw [if_neg hn, if_neg hn, zero_mul]

/-- Step 1 identification: given the bounded partial sums, the by-parts series of `fSub c`
is `A(s) - c·P(s)` for `Re s > 1`. -/
lemma bpSeries_fSub_eq {c C : ℝ}
    (hC' : ∀ n, ‖∑ k ∈ Finset.range (n + 1), fSub c k‖ ≤ C) {s : ℂ} (hs : 1 < s.re) :
    bpSeries (fSub c) s
      = layerA s - (c : ℂ) * ∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-s) := by
  have hfChi := summable_fChi_mul_cpow hs
  have hind := summable_ite_prime_mul_cpow hs
  calc bpSeries (fSub c) s
      = ∑' n : ℕ, fSub c n * (n : ℂ) ^ (-s) := (tsum_mul_cpow_neg_eq_bpSeries hC' hs).symm
    _ = ∑' n : ℕ, (fChi n * (n : ℂ) ^ (-s)
          - (c : ℂ) * ((if n.Prime then (1 : ℂ) else 0) * (n : ℂ) ^ (-s))) := by
        refine tsum_congr fun n ↦ ?_
        unfold fSub
        ring
    _ = (∑' n : ℕ, fChi n * (n : ℂ) ^ (-s))
          - ∑' n : ℕ, (c : ℂ) * ((if n.Prime then (1 : ℂ) else 0) * (n : ℂ) ^ (-s)) :=
        hfChi.tsum_sub (hind.mul_left _)
    _ = layerA s - (c : ℂ) * ∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-s) := by
        rw [layerA_eq_tsum_fChi, tsum_mul_left, tsum_primes_cpow_eq_tsum_ite]

/-- Step 1: the real prime series `P(σ) = Σ_p p^(-σ)` (PROOF.md case c ≠ 0). -/
noncomputable def primeSum (σ : ℝ) : ℝ := ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ)

/-- `P(σ)` is the real restriction of the complex prime series (unconditional
`Complex.ofReal_tsum` pattern, as in `layerA_ofReal`). -/
lemma primeSum_ofReal (σ : ℝ) :
    ∑' p : Nat.Primes, ((p : ℕ) : ℂ) ^ (-(σ : ℂ)) = ((primeSum σ : ℝ) : ℂ) := by
  unfold primeSum
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun p ↦ ?_
  rw [Complex.ofReal_cpow (Nat.cast_nonneg _)]
  push_cast
  rfl

/-- PROOF.md c≠0 **step 1** (Abel bound, real form): under the linearity hypothesis,
`|A(σ) - c·P(σ)| ≤ C` for real `σ > 1`. -/
lemma abs_layerAReal_sub_mul_primeSum_le {c C : ℝ}
    (hC : ∀ N : ℕ, |(raceSum N : ℝ) - c * (Nat.primeCounting N : ℝ)| ≤ C)
    {σ : ℝ} (hσ : 1 < σ) :
    |layerAReal σ - c * primeSum σ| ≤ C := by
  have hC' := norm_sum_range_fSub_le hC
  have hb := norm_bpSeries_le_const hC' (n₀ := 2) (by norm_num)
    (sum_range_fSub_eq_zero c) (show (0 : ℝ) ≤ σ by linarith)
  have hs : 1 < ((σ : ℂ)).re := by rwa [Complex.ofReal_re]
  have hid : bpSeries (fSub c) (σ : ℂ)
      = ((layerAReal σ - c * primeSum σ : ℝ) : ℂ) := by
    rw [bpSeries_fSub_eq hC' hs, layerA_ofReal, primeSum_ofReal σ]
    push_cast
    ring
  rw [hid, Complex.norm_real, Real.norm_eq_abs] at hb
  exact hb

/-! ## Step 2: `layerAReal` is bounded on `(1, 2]` (PROOF.md c≠0 step 2) -/

/-- Step 2: on the real axis right of `1`, the continued `L(χ, σ)` is the cast of the
positive real number `exp (A(σ) + B(σ) + T(σ))` (Euler wiring + the three `ofReal`
lemmas). -/
lemma LFunction_ofReal_eq_exp {σ : ℝ} (hσ : 1 < σ) :
    DirichletCharacter.LFunction χ (σ : ℂ)
      = ((Real.exp (layerAReal σ + layerBReal σ + layerTReal σ) : ℝ) : ℂ) := by
  have hs : 1 < ((σ : ℂ)).re := by rwa [Complex.ofReal_re]
  rw [← exp_layers_eq_LFunction hs, layerA_ofReal, layerB_ofReal, layerT_ofReal,
    ← Complex.ofReal_add, ← Complex.ofReal_add, Complex.ofReal_exp]

/-- Step 2: `Re L(χ, σ) > 0` for real `σ > 1`. -/
lemma LFunction_ofReal_re_pos {σ : ℝ} (hσ : 1 < σ) :
    0 < (DirichletCharacter.LFunction χ (σ : ℂ)).re := by
  rw [LFunction_ofReal_eq_exp hσ, Complex.ofReal_re]
  exact Real.exp_pos _

/-- Step 2: `Im L(χ, σ) = 0` for real `σ > 1`. -/
lemma LFunction_ofReal_im_eq_zero {σ : ℝ} (hσ : 1 < σ) :
    (DirichletCharacter.LFunction χ (σ : ℂ)).im = 0 := by
  rw [LFunction_ofReal_eq_exp hσ, Complex.ofReal_im]

/-- Step 2: continuity of `σ ↦ Re L(χ, σ)` on the real line (M2 differentiability). -/
lemma continuous_LFunction_ofReal_re :
    Continuous fun σ : ℝ ↦ (DirichletCharacter.LFunction χ (σ : ℂ)).re :=
  Complex.continuous_re.comp
    ((DirichletCharacter.differentiable_LFunction χ_ne_one).continuous.comp
      Complex.continuous_ofReal)

/-- Step 2: continuity of `σ ↦ Im L(χ, σ)` on the real line. -/
lemma continuous_LFunction_ofReal_im :
    Continuous fun σ : ℝ ↦ (DirichletCharacter.LFunction χ (σ : ℂ)).im :=
  Complex.continuous_im.comp
    ((DirichletCharacter.differentiable_LFunction χ_ne_one).continuous.comp
      Complex.continuous_ofReal)

/-- Step 2 (M3 + one-sided limits): `Re L(χ, 1) > 0`.  The imaginary part at `1` is a limit
of zeros, the real part a limit of positive values, and the complex value is nonzero by M3
(`DirichletCharacter.LFunction_apply_one_ne_zero`). -/
lemma LFunction_one_re_pos : 0 < (DirichletCharacter.LFunction χ ((1 : ℝ) : ℂ)).re := by
  have him : (DirichletCharacter.LFunction χ ((1 : ℝ) : ℂ)).im = 0 := by
    have h1 : Tendsto (fun σ : ℝ ↦ (DirichletCharacter.LFunction χ (σ : ℂ)).im)
        (𝓝[>] 1) (𝓝 ((DirichletCharacter.LFunction χ ((1 : ℝ) : ℂ)).im)) :=
      (continuous_LFunction_ofReal_im.tendsto 1).mono_left nhdsWithin_le_nhds
    have h2 : Tendsto (fun σ : ℝ ↦ (DirichletCharacter.LFunction χ (σ : ℂ)).im)
        (𝓝[>] 1) (𝓝 0) :=
      Tendsto.congr' (eventually_nhdsWithin_of_forall
        fun σ hσ ↦ (LFunction_ofReal_im_eq_zero (Set.mem_Ioi.mp hσ)).symm) tendsto_const_nhds
    exact tendsto_nhds_unique h1 h2
  have hre0 : 0 ≤ (DirichletCharacter.LFunction χ ((1 : ℝ) : ℂ)).re := by
    have h1 : Tendsto (fun σ : ℝ ↦ (DirichletCharacter.LFunction χ (σ : ℂ)).re)
        (𝓝[>] 1) (𝓝 ((DirichletCharacter.LFunction χ ((1 : ℝ) : ℂ)).re)) :=
      (continuous_LFunction_ofReal_re.tendsto 1).mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto h1 (eventually_nhdsWithin_of_forall fun σ hσ ↦ ?_)
    exact (LFunction_ofReal_re_pos (Set.mem_Ioi.mp hσ)).le
  have hne : (DirichletCharacter.LFunction χ ((1 : ℝ) : ℂ)).re ≠ 0 := by
    intro h0
    apply DirichletCharacter.LFunction_apply_one_ne_zero χ_ne_one
    rw [show (1 : ℂ) = ((1 : ℝ) : ℂ) from Complex.ofReal_one.symm]
    exact Complex.ext (by rw [h0, Complex.zero_re]) (by rw [him, Complex.zero_im])
  exact lt_of_le_of_ne hre0 (Ne.symm hne)

/-- Step 2: `Re L(χ, σ) > 0` on the compact `[1, 2]`. -/
lemma LFunction_ofReal_re_pos_of_mem_Icc {σ : ℝ} (hσ : σ ∈ Set.Icc (1 : ℝ) 2) :
    0 < (DirichletCharacter.LFunction χ (σ : ℂ)).re := by
  rcases eq_or_lt_of_le hσ.1 with h1 | h1
  · rw [← h1]
    exact LFunction_one_re_pos
  · exact LFunction_ofReal_re_pos h1

/-- Step 2: `A(σ) = log (Re L(χ, σ)) - B(σ) - T(σ)` for real `σ > 1` (real `exp`
inverted with `Real.log_exp`; no complex logarithm involved). -/
lemma layerAReal_eq_log_sub {σ : ℝ} (hσ : 1 < σ) :
    layerAReal σ
      = Real.log ((DirichletCharacter.LFunction χ (σ : ℂ)).re)
        - layerBReal σ - layerTReal σ := by
  have h : (DirichletCharacter.LFunction χ (σ : ℂ)).re
      = Real.exp (layerAReal σ + layerBReal σ + layerTReal σ) := by
    rw [LFunction_ofReal_eq_exp hσ, Complex.ofReal_re]
  rw [h, Real.log_exp]
  ring

/-- PROOF.md c≠0 **step 2**: a uniform bound `|A(σ)| ≤ K` on `(1, 2]`, from continuity and
positivity of `Re L(χ, ·)` on the compact `[1, 2]` plus the `B`/`T` bounds. -/
lemma exists_bound_abs_layerAReal :
    ∃ K : ℝ, ∀ σ : ℝ, 1 < σ → σ ≤ 2 → |layerAReal σ| ≤ K := by
  obtain ⟨K₀, hK₀⟩ := (isCompact_Icc (a := (1 : ℝ)) (b := 2)).exists_bound_of_continuousOn
    (continuous_LFunction_ofReal_re.continuousOn.log
      fun σ hσ ↦ (LFunction_ofReal_re_pos_of_mem_Icc hσ).ne')
  refine ⟨K₀ + C_B + C_T, fun σ h1 h2 ↦ ?_⟩
  have hlog : |Real.log ((DirichletCharacter.LFunction χ (σ : ℂ)).re)| ≤ K₀ := by
    have h := hK₀ σ (Set.mem_Icc.mpr ⟨h1.le, h2⟩)
    rw [Real.norm_eq_abs] at h
    exact h
  rw [abs_le] at hlog
  have hB1 : layerBReal σ ≤ C_B := layerBReal_le_C_B h1.le
  have hB0 : 0 ≤ layerBReal σ := layerBReal_nonneg σ
  have hT := abs_layerTReal_le (show 1 / 2 ≤ σ by linarith)
  rw [abs_le] at hT
  rw [layerAReal_eq_log_sub h1, abs_le]
  constructor
  · linarith [hlog.1, hT.2]
  · linarith [hlog.2, hT.1]

/-! ## Step 3: conclusion (PROOF.md c≠0 step 3) -/

/-- **Case `c ≠ 0` of PROOF.md Step D** (steps 1–3): if the race sum is `c·π + O(1)`, then
`c = 0`.  Entry point for track 4e, which uses it to reduce `raceSum_not_linear` to the
bounded-race case `|raceSum N| ≤ C`.

If `c ≠ 0`, steps 1–2 give `|c|·P(σ) ≤ C + K` for all `σ ∈ (1, 2]`, but R1
(`exists_one_lt_tsum_primes_rpow_gt`, the sole prime input `Σ 1/p = ∞`) produces a single
`σ ∈ (1, 2)` where `P(σ) > (C + K)/|c|`.  Contradiction. -/
theorem c_eq_zero_of_raceSum_linear {c C : ℝ}
    (hC : ∀ N : ℕ, |(raceSum N : ℝ) - c * (Nat.primeCounting N : ℝ)| ≤ C) : c = 0 := by
  by_contra hc
  obtain ⟨K, hK⟩ := exists_bound_abs_layerAReal
  have hcpos : 0 < |c| := abs_pos.mpr hc
  obtain ⟨σ, hσ1, hσ2, hσP⟩ :=
    exists_one_lt_tsum_primes_rpow_gt ((C + K) / |c|) (η := 1) one_pos
  have hσP' : (C + K) / |c| < primeSum σ := hσP
  have hstep1 := abs_layerAReal_sub_mul_primeSum_le hC hσ1
  have hstep2 := hK σ hσ1 (by linarith)
  rw [abs_le] at hstep1 hstep2
  have hPnonneg : 0 ≤ primeSum σ :=
    tsum_nonneg fun p ↦ Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hgt : C + K < |c| * primeSum σ := by
    have h := (div_lt_iff₀ hcpos).mp hσP'
    linarith [mul_comm (primeSum σ) (|c|)]
  have hle : |c| * primeSum σ ≤ C + K := by
    have habs : |c * primeSum σ| ≤ C + K := by
      have hrew : c * primeSum σ = layerAReal σ - (layerAReal σ - c * primeSum σ) := by ring
      rw [hrew, abs_le]
      exact ⟨by linarith [hstep1.2, hstep2.1], by linarith [hstep1.1, hstep2.2]⟩
    calc |c| * primeSum σ = |c| * |primeSum σ| := by rw [abs_of_nonneg hPnonneg]
      _ = |c * primeSum σ| := (abs_mul c (primeSum σ)).symm
      _ ≤ C + K := habs
  linarith

end A362583
