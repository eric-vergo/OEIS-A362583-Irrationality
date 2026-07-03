import Mathlib.Analysis.Complex.LocallyUniformLimit

/-! M9: holomorphy of locally uniform limits of partial sums (spec §4) -/

open Filter Topology

-- Weierstrass: locally uniform limit of holomorphic functions is holomorphic.
#check @TendstoLocallyUniformlyOn.differentiableOn
-- Tsum variant with a uniform summable norm bound (note: `Complex` namespace).
#check @Complex.differentiableOn_tsum_of_summable_norm

/-- D1 skeleton: if the partial sums of a Dirichlet-series-shaped family
converge locally uniformly on an open `U`, the limit is holomorphic on `U`.
`φ = atTop : Filter ℕ` supplies the required `[φ.NeBot]` instance. -/
example {f : ℕ → ℂ → ℂ} {g : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ k : ℕ, DifferentiableOn ℂ (f k) U)
    (hlim : TendstoLocallyUniformlyOn
      (fun (n : ℕ) (s : ℂ) => ∑ k ∈ Finset.range n, f k s) g atTop U) :
    DifferentiableOn ℂ g U :=
  hlim.differentiableOn
    (Eventually.of_forall fun _n => DifferentiableOn.fun_sum fun k _ => hf k) hU

/- Exact statement (Mathlib/Analysis/Complex/LocallyUniformLimit.lean:170,
inside `namespace Complex`):
`theorem Complex.differentiableOn_tsum_of_summable_norm {u : ι → ℝ} (hu : Summable u)
    (hf : ∀ i : ι, DifferentiableOn ℂ (F i) U) (hU : IsOpen U)
    (hF_le : ∀ (i : ι) (w : ℂ), w ∈ U → ‖F i w‖ ≤ u i) :
    DifferentiableOn ℂ (fun w : ℂ => ∑' i : ι, F i w) U`
Shortcut assessment for N1 (Dirichlet series with bounded partial sums on
`{δ < s.re}`): NOT directly usable, because it requires a single summable bound
`u` valid on all of `U`, while the termwise bound `‖a n / n ^ s‖ ≤ C / n ^ δ`
fails to be summable for `δ ≤ 1` — bounded partial sums / Abel summation give
convergence there without termwise summability, so M9's Weierstrass route
(`TendstoLocallyUniformlyOn.differentiableOn` on the partial sums) is the one
that matches D1. -/
