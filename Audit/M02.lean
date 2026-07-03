import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-! M2: continued L-function; entire for nonprincipal; = LSeries on Re s > 1 (spec §4) -/

namespace Audit.M02

open Complex

/-- The nontrivial Dirichlet character mod 4 (proved nontrivial in `Audit/M01.lean`). -/
noncomputable def χ : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

lemma χ_ne_one : χ ≠ 1 := by
  refine (MulChar.ringHomComp_ne_one_iff (Int.castRingHom ℂ).injective_int).mpr fun h ↦ ?_
  have h3 : (1 : MulChar (ZMod 4) ℤ) ((3 : ℕ) : ZMod 4) = -1 :=
    h ▸ ZMod.χ₄_nat_three_mod_four (by norm_num)
  rw [MulChar.one_apply (IsUnit.of_mul_eq_one 3 (by decide))] at h3
  norm_num at h3

-- The analytically continued L-function (defined as `ZMod.LFunction χ`):
#check (DirichletCharacter.LFunction χ : ℂ → ℂ)
#check @DirichletCharacter.differentiable_LFunction
-- ∀ {N : ℕ} [inst : NeZero N] {χ : DirichletCharacter ℂ N},
--   χ ≠ 1 → Differentiable ℂ (DirichletCharacter.LFunction χ)   (χ IMPLICIT here)
#check @DirichletCharacter.LFunction_eq_LSeries
-- ∀ {N : ℕ} [inst : NeZero N] (χ : DirichletCharacter ℂ N) {s : ℂ},
--   1 < s.re → DirichletCharacter.LFunction χ s = LSeries (fun x => χ ↑x) s   (χ EXPLICIT here)

example : Differentiable ℂ (DirichletCharacter.LFunction χ) :=
  DirichletCharacter.differentiable_LFunction χ_ne_one

example {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction χ s = LSeries (fun n : ℕ ↦ χ n) s :=
  DirichletCharacter.LFunction_eq_LSeries χ hs

end Audit.M02
