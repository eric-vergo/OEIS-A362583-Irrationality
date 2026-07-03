import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-! M4: Euler product, exp form (spec §4, risk R2) -/

namespace Audit.M04

open Complex

/-- The nontrivial Dirichlet character mod 4 (proved nontrivial in `Audit/M01.lean`). -/
noncomputable def χ : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

#check @DirichletCharacter.LSeries_eulerProduct_exp_log
-- ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) {s : ℂ},
--   1 < s.re → cexp (∑' (p : Nat.Primes), -log (1 - χ ↑↑p * ↑↑p ^ (-s))) = LSeries (fun n => χ ↑n) s

/- Elaboration notes (checked with `set_option pp.explicit true`):
* `χ ↑↑p` is `χ ((((p : Nat.Primes).val : ℕ) : ZMod 4))`: outer `Nat.cast : ℕ → ZMod 4`
  applied to `Subtype.val : Nat.Primes → ℕ`.  There is no direct `Nat.Primes → ZMod 4` coercion.
* `↑↑p ^ (-s)` is `(((p.val : ℕ) : ℂ)) ^ (-s)`: the base is `Nat.cast (p : ℕ) : ℂ`
  (a ℕ-cast into ℂ, NOT a `Nat.Primes`-cast), and `^` is the `Monoid.Pow ℂ ℂ` instance
  coming from `Complex.instPow`, i.e. `Complex.cpow`.
* `L ↗χ s` (scoped notation `LSeries.notation`) unfolds to `LSeries (fun n : ℕ ↦ (χ ↑n : ℂ)) s`,
  the same term as the `LSeries (χ ·) s` in `DirichletCharacter.LFunction_eq_LSeries`,
  so the two chain by plain `rw`/`exact` — no fallback assembly from
  `EulerProduct.exp_tsum_primes_log_eq_tsum` + `summable_dirichletSummand` is needed.
-/

-- Direct instantiation at our χ: a one-line `exact`.
example {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -log (1 - χ p * p ^ (-s))) = LSeries (fun n : ℕ ↦ χ n) s :=
  DirichletCharacter.LSeries_eulerProduct_exp_log χ hs

-- Chained to the continued L-function via M2's `LFunction_eq_LSeries`.
example {s : ℂ} (hs : 1 < s.re) :
    exp (∑' p : Nat.Primes, -log (1 - χ p * p ^ (-s))) = DirichletCharacter.LFunction χ s := by
  rw [DirichletCharacter.LFunction_eq_LSeries χ hs]
  exact DirichletCharacter.LSeries_eulerProduct_exp_log χ hs

end Audit.M04
