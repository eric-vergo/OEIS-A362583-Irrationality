/-
Copyright (c) 2026 Eric Vergo. Dedicated to the public domain.
Released under CC0 1.0 Universal as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import A362583.Layers

/-!
# Euler product / L-function wiring for Step D

The `k = 1` layer `A(s)` and the two consolidated Step D identities on `{Re s > 1}`:

* **Per-`p` split summed over primes**: `tsum_neg_log_eq_layers`,
  `Σ_p -log(1 - χ(p) p^(-s)) = A(s) + B(s) + T(s)` — the per-prime split
  `neg_log_split` summed with linearity of three absolutely convergent series
  (no double-sum rearrangement).
* **Euler wiring**: `exp_layers_eq_LFunction`,
  `exp (A(s) + B(s) + T(s)) = L(s, χ)` for the analytically continued
  `DirichletCharacter.LFunction`, via `DirichletCharacter.LSeries_eulerProduct_exp_log`
  and `DirichletCharacter.LFunction_eq_LSeries`.

Bridges consumed by the later Step D tracks:

* `fChi`, `sum_range_fChi`, `layerA_eq_tsum_fChi` — the ℕ-indexed form of `A(s)`
  whose partial sums are exactly `raceSum` (feeds the by-parts continuation
  `Complex.bpSeries fChi` of `A362583/BoundedHolo.lean`).
* `layerAReal`, `layerA_ofReal`, `layerA_re`, `layerA_im` — real companion on the
  real axis, in the unconditional `Complex.ofReal_tsum` style of `layerB_ofReal`.
-/

namespace A362583

open Complex

/-! ## The k = 1 layer `A` -/

/-- The `k = 1` layer `A(s) = Σ_p χ(p) p^(-s)`. -/
noncomputable def layerA (s : ℂ) : ℂ :=
  ∑' p : Nat.Primes, χ ((p : ℕ) : ZMod 4) * ((p : ℕ) : ℂ) ^ (-s)

/-- Summability of the `layerA` integrand for `Re s > 1`. -/
lemma summable_layerA_term {s : ℂ} (hs : 1 < s.re) :
    Summable (fun p : Nat.Primes ↦ χ ((p : ℕ) : ZMod 4) * ((p : ℕ) : ℂ) ^ (-s)) :=
  (summable_norm_term_one hs).of_norm

/-! ## The per-p split summed over primes -/

/-- **Per-`p` split summed over primes**: for `Re s > 1`,
`Σ_p -log(1 - χ(p) p^(-s)) = A(s) + B(s) + T(s)`.
Proof: rewrite each term with the per-prime split `neg_log_split`, then split the sum
by linearity of three absolutely convergent series (`Summable.tsum_add` twice) and
identify the `k = 2` piece as `layerB` (`tsum_term_two_eq_layerB`).
No double-sum rearrangement is involved. -/
theorem tsum_neg_log_eq_layers {s : ℂ} (hs : 1 < s.re) :
    ∑' p : Nat.Primes, -Complex.log (1 - χ ((p : ℕ) : ZMod 4) * ((p : ℕ) : ℂ) ^ (-s))
      = layerA s + layerB s + layerT s := by
  have h1 : Summable (fun p : Nat.Primes ↦ χ ((p : ℕ) : ZMod 4) * ((p : ℕ) : ℂ) ^ (-s)) :=
    summable_layerA_term hs
  have h2 : Summable
      (fun p : Nat.Primes ↦ χ ((p : ℕ) : ZMod 4) ^ 2 * ((p : ℕ) : ℂ) ^ (-(2 * s)) / 2) :=
    (summable_norm_term_two (by linarith)).of_norm
  have h3 : Summable (fun p : Nat.Primes ↦ tp p s) := summable_tp (by linarith)
  calc ∑' p : Nat.Primes, -Complex.log (1 - χ ((p : ℕ) : ZMod 4) * ((p : ℕ) : ℂ) ^ (-s))
      = ∑' p : Nat.Primes, (χ ((p : ℕ) : ZMod 4) * ((p : ℕ) : ℂ) ^ (-s)
          + χ ((p : ℕ) : ZMod 4) ^ 2 * ((p : ℕ) : ℂ) ^ (-(2 * s)) / 2 + tp p s) :=
        tsum_congr fun p ↦ neg_log_split p hs
    _ = (∑' p : Nat.Primes, (χ ((p : ℕ) : ZMod 4) * ((p : ℕ) : ℂ) ^ (-s)
          + χ ((p : ℕ) : ZMod 4) ^ 2 * ((p : ℕ) : ℂ) ^ (-(2 * s)) / 2))
          + ∑' p : Nat.Primes, tp p s := (h1.add h2).tsum_add h3
    _ = ((∑' p : Nat.Primes, χ ((p : ℕ) : ZMod 4) * ((p : ℕ) : ℂ) ^ (-s))
          + ∑' p : Nat.Primes, χ ((p : ℕ) : ZMod 4) ^ 2 * ((p : ℕ) : ℂ) ^ (-(2 * s)) / 2)
          + ∑' p : Nat.Primes, tp p s := by rw [h1.tsum_add h2]
    _ = layerA s + layerB s + layerT s := by rw [tsum_term_two_eq_layerB]; rfl

/-! ## The Euler wiring -/

/-- **Euler wiring**: for `Re s > 1`,
`exp (A(s) + B(s) + T(s)) = L(s, χ)` with `L` the analytically continued
`DirichletCharacter.LFunction`.  This is `tsum_neg_log_eq_layers` + the exp-form Euler
product (`DirichletCharacter.LSeries_eulerProduct_exp_log`) + the identification of
`LFunction` with the Dirichlet series on `Re s > 1`
(`DirichletCharacter.LFunction_eq_LSeries`). -/
theorem exp_layers_eq_LFunction {s : ℂ} (hs : 1 < s.re) :
    Complex.exp (layerA s + layerB s + layerT s) = DirichletCharacter.LFunction χ s := by
  rw [← tsum_neg_log_eq_layers hs, DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact DirichletCharacter.LSeries_eulerProduct_exp_log χ hs

/-! ## ℕ-indexed bridge (feeds the by-parts continuation of `BoundedHolo.lean`) -/

/-- Bridge: the ℕ-indexed coefficient function of `layerA` — `raceKernel n` at
primes, `0` elsewhere.  Its partial sums are exactly `raceSum` (`sum_range_fChi`),
so `Complex.bpSeries fChi` is the by-parts continuation of `layerA`
(via `layerA_eq_tsum_fChi` + `Complex.tsum_mul_cpow_neg_eq_bpSeries`). -/
noncomputable def fChi (n : ℕ) : ℂ := if n.Prime then ((raceKernel n : ℤ) : ℂ) else 0

/-- `fChi 0 = 0` (`0` is not prime). -/
lemma fChi_zero : fChi 0 = 0 := by
  unfold fChi
  rw [if_neg Nat.not_prime_zero]

/-- `fChi 1 = 0` (`1` is not prime). -/
lemma fChi_one : fChi 1 = 0 := by
  unfold fChi
  rw [if_neg Nat.not_prime_one]

/-- Bridge: the partial sums of `fChi` are exactly the race sums,
`Σ_{k ≤ n} fChi k = raceSum n` (as complex numbers). -/
lemma sum_range_fChi (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), fChi k = ((raceSum n : ℤ) : ℂ) := by
  unfold fChi
  rw [raceSum_eq_sum_raceKernel, ← Finset.sum_filter]
  push_cast
  rfl

/-- Bridge: `layerA` as a ℕ-indexed Dirichlet series,
`A(s) = Σ_n fChi n · n^(-s)` (unconditional: subtype ↔ indicator `tsum` bridge;
both sides converge absolutely for `Re s > 1`, but no summability is needed). -/
lemma layerA_eq_tsum_fChi (s : ℂ) :
    layerA s = ∑' n : ℕ, fChi n * (n : ℂ) ^ (-s) := by
  have h := tsum_subtype {n : ℕ | n.Prime}
    (fun n : ℕ ↦ χ (n : ZMod 4) * (n : ℂ) ^ (-s))
  calc layerA s
      = ∑' n : ℕ, Set.indicator {n : ℕ | n.Prime}
          (fun n : ℕ ↦ χ (n : ZMod 4) * (n : ℂ) ^ (-s)) n := h
    _ = ∑' n : ℕ, fChi n * (n : ℂ) ^ (-s) := by
        refine tsum_congr fun n ↦ ?_
        rw [Set.indicator_apply]
        simp only [Set.mem_setOf_eq]
        unfold fChi
        by_cases hn : n.Prime
        · rw [if_pos hn, if_pos hn, χ_natCast_eq_kernel]
        · rw [if_neg hn, if_neg hn, zero_mul]

/-! ## Real companion on the real axis (consumed by the Step D endgame) -/

/-- Real companion of `layerA` (real `rpow`; agreement: `layerA_ofReal`). -/
noncomputable def layerAReal (σ : ℝ) : ℝ :=
  ∑' p : Nat.Primes, ((raceKernel (p : ℕ) : ℤ) : ℝ) * ((p : ℕ) : ℝ) ^ (-σ)

/-- For real `σ`, `layerA` is the cast of `layerAReal` (unconditional). -/
lemma layerA_ofReal (σ : ℝ) : layerA (σ : ℂ) = ((layerAReal σ : ℝ) : ℂ) := by
  unfold layerA layerAReal
  rw [Complex.ofReal_tsum]
  refine tsum_congr fun p ↦ ?_
  rw [Complex.ofReal_mul, Complex.ofReal_cpow (Nat.cast_nonneg _), χ_natCast_eq_kernel]
  push_cast
  rfl

/-- `layerA` is real on the real axis. -/
lemma layerA_im (σ : ℝ) : (layerA (σ : ℂ)).im = 0 := by
  rw [layerA_ofReal]; exact Complex.ofReal_im _

/-- Real part of `layerA` on the real axis. -/
lemma layerA_re (σ : ℝ) : (layerA (σ : ℂ)).re = layerAReal σ := by
  rw [layerA_ofReal]; exact Complex.ofReal_re _

end A362583
