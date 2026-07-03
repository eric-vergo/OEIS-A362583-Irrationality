import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Convex.PathConnected

/-! M8: identity theorem on the half-plane Ω = {s | 1/2 < s.re} (spec §4) -/

open Set Filter Topology

-- Core identity theorem and the holomorphic → analytic entry point.
#check @AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
#check @DifferentiableOn.analyticOnNhd
-- (a) Ω open: `isOpen_lt continuous_const Complex.continuous_re`.
#check (isOpen_lt continuous_const Complex.continuous_re :
  IsOpen {s : ℂ | (1/2 : ℝ) < s.re})
-- (b) Ω preconnected via convexity: `convex_halfSpace_re_gt` (root namespace,
--     explicit `r`) + `Convex.isPreconnected`.
#check ((convex_halfSpace_re_gt (1/2 : ℝ)).isPreconnected :
  IsPreconnected {s : ℂ | (1/2 : ℝ) < s.re})
-- (c) agreement on an open subset → `f =ᶠ[𝓝 z₀] g`.
#check @Filter.eventuallyEq_of_mem
#check @IsOpen.mem_nhds

/-- D3 skeleton: `f g` holomorphic on `Ω = {s | 1/2 < s.re}` agreeing on
`{s | 1 < s.re}` agree on all of `Ω`. -/
example {f g : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {s : ℂ | (1/2 : ℝ) < s.re})
    (hg : DifferentiableOn ℂ g {s : ℂ | (1/2 : ℝ) < s.re})
    (hfg : Set.EqOn f g {s : ℂ | 1 < s.re}) :
    Set.EqOn f g {s : ℂ | (1/2 : ℝ) < s.re} := by
  have hΩ : IsOpen {s : ℂ | (1/2 : ℝ) < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hO : IsOpen {s : ℂ | 1 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hpre : IsPreconnected {s : ℂ | (1/2 : ℝ) < s.re} :=
    (convex_halfSpace_re_gt (1/2 : ℝ)).isPreconnected
  -- (d) membership side goals for the anchor point `2`.
  have h₂O : (2 : ℂ) ∈ {s : ℂ | 1 < s.re} := by
    norm_num [Set.mem_setOf_eq]
  have h₂Ω : (2 : ℂ) ∈ {s : ℂ | (1/2 : ℝ) < s.re} := by
    norm_num [Set.mem_setOf_eq]
  have hev : f =ᶠ[𝓝 (2 : ℂ)] g :=
    Filter.eventuallyEq_of_mem (hO.mem_nhds h₂O) hfg
  exact (hf.analyticOnNhd hΩ).eqOn_of_preconnected_of_eventuallyEq
    (hg.analyticOnNhd hΩ) hpre h₂Ω hev
