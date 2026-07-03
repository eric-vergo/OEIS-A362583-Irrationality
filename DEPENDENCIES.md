# DEPENDENCIES.md — Mathlib dependency audit (spec §4)

Pinned toolchain: `leanprover/lean4:v4.31.0`.
Pinned Mathlib: tag `v4.31.0` (rev `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`).

Status legend: **verified-by-grep, MWE pending** = declaration name confirmed to exist
at v4.31.0 by source inspection; a minimal working example in `Audit/` is still owed
(Phase 0c). **TO VERIFY** = not yet audited. **expected ABSENT** = plan assumes it is
not in Mathlib.

| Item | Ingredient | Verified Mathlib name(s) | Module | Status | Notes |
|---|---|---|---|---|---|
| M1 | χ₄ as a character; value lemmas; bridge to ℂ | `ZMod.χ₄ : MulChar (ZMod 4) ℤ`; `ZMod.χ₄_nat_eq_if_mod_four`, `ZMod.χ₄_nat_one_mod_four`, `ZMod.χ₄_nat_three_mod_four`, `ZMod.χ₄_nat_mod_four`; `MulChar.ringHomComp`, `MulChar.ringHomComp_apply`, `MulChar.ringHomComp_ne_one_iff` | `Mathlib.NumberTheory.LegendreSymbol.ZModChar`, `Mathlib.NumberTheory.MulChar.Basic` | verified-by-grep, MWE pending | Bridge to `DirichletCharacter ℂ 4` via `MulChar.ringHomComp (Int.castRingHom ℂ)`; values via `MulChar.ringHomComp_apply`; nontriviality via `MulChar.ringHomComp_ne_one_iff` + `Int.cast_injective`. |
| M2 | Continued L-function; entire for nonprincipal; = LSeries on Re s > 1 | `DirichletCharacter.LFunction`; `DirichletCharacter.differentiable_LFunction (hχ : χ ≠ 1)`; `DirichletCharacter.LFunction_eq_LSeries (hs : 1 < re s)` | `Mathlib.NumberTheory.LSeries.DirichletContinuation` | verified-by-grep, MWE pending | `differentiable_LFunction` gives entire for χ ≠ 1. |
| M3 | L(1,χ) ≠ 0 for nonprincipal χ | `DirichletCharacter.LFunction_apply_one_ne_zero (hχ : χ ≠ 1)`; stronger: `DirichletCharacter.LFunction_ne_zero_of_re_eq_one`, `DirichletCharacter.LFunction_ne_zero_of_one_le_re` | `Mathlib.NumberTheory.LSeries.Nonvanishing` | verified-by-grep, MWE pending | The `…_of_one_le_re` variants take strict-implicit `⦃s⦄`; hypothesis order is hχs then hs. |
| M4 | Euler product, exp form | `DirichletCharacter.LSeries_eulerProduct_exp_log : exp (∑' p : Nat.Primes, -log (1 - χ p * p ^ (-s))) = L ↗χ s` for `1 < s.re`; companions `LSeries_eulerProduct_hasProd`, `LSeries_eulerProduct_tprod`, `LSeries_eulerProduct` | `Mathlib.NumberTheory.EulerProduct.DirichletLSeries` | verified-by-grep, MWE pending | Sum is over subtype `Nat.Primes`; log is `Complex.log`; RHS is `LSeries` — chain with M2's `LFunction_eq_LSeries` to reach `LFunction`. |
| M5 | ∑ 1/p = ∞ | `Nat.Primes.not_summable_one_div`; `not_summable_one_div_on_primes`; `Nat.Primes.summable_rpow : Summable (fun p : Nat.Primes ↦ (p:ℝ) ^ r) ↔ r < -1` | `Mathlib.NumberTheory.SumPrimeReciprocals` | verified-by-grep, MWE pending | |
| M6 | Infinitely many primes ≡ 1 and ≡ 3 (mod 4) | `Nat.infinite_setOf_prime_and_eq_mod (ha : IsUnit a)`; also `Nat.forall_exists_prime_gt_and_eq_mod` | `Mathlib.NumberTheory.LSeries.PrimesInAP` | verified-by-grep, MWE pending | No elementary 3-mod-4 lemma exists in Mathlib — use the general Dirichlet theorem (L-stack imported anyway). |
| M7 | `Nat.nth` / `Nat.count` prime-indexing machinery | `Nat.count p n` counts k < n (strict); `Nat.primeCounting n` = # primes ≤ n = `Nat.count Nat.Prime (n+1)`; `Nat.primeCounting'` strict; `Nat.nth_count`, `Nat.count_nth`, `Nat.nth_lt_nth`, `Nat.gc_count_nth`, `Nat.count_le_iff_le_nth`, `Nat.primeCounting'_nth_eq` | `Mathlib.Data.Nat.Count`, `Mathlib.Data.Nat.Nth`, `Mathlib.NumberTheory.PrimeCounting` | verified-by-grep, MWE pending | `Nat.count_nth`-style hypotheses are vacuous for infinite predicates: discharge with `fun hf ↦ absurd hf hp`. |
| M8 | Identity theorem | `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` + `DifferentiableOn.analyticOnNhd` | `Mathlib.Analysis.Analytic.Uniqueness` | verified-by-grep, MWE pending | Post-2024 rename: old `AnalyticOn` → `AnalyticOnNhd`. |
| M9 | Locally uniform limits of holomorphic are holomorphic | `TendstoLocallyUniformlyOn.differentiableOn` (+ `.deriv`); bonus `differentiableOn_tsum_of_summable_norm` | `Mathlib.Analysis.Complex.LocallyUniformLimit` | verified-by-grep, MWE pending | The bonus lemma may shortcut N1. |
| M10 | Summation by parts (discrete Abel) | `Finset.sum_Ioc_by_parts` (stated with `•` over a Module, `range (·+1)` prefix sums); integral forms `sum_mul_eq_sub_sub_integral_mul` etc. | `Mathlib.Algebra.BigOperators.Module`, `Mathlib.NumberTheory.AbelSummation` | verified-by-grep, MWE pending | |
| M11 | `Int.fract` API (fract of rationals has denominator b; fract(2·) arithmetic) | — | — | TO VERIFY (Phase 0c) | |
| M12 | `‖(n:ℂ)^(-s)‖` norm lemmas; increment bound | `Complex.norm_natCast_cpow_*` — TO VERIFY | — | TO VERIFY (Phase 0c) | Increment bound `\|n^{-s}-(n+1)^{-s}\| ≤ \|s\| n^{-σ-1}` likely absent → plan FTC mini-lemma. |
| M13 | tsum toolkit (`tsum_sigma`, `Summable.tsum_prod`, comparison tests) | — | — | TO VERIFY (Phase 0c) | |
| M14 | Rational ⟺ eventually periodic binary digits | — | — | expected ABSENT | Step B pigeonhole (N2) planned regardless. |
