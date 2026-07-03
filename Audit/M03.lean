import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LegendreSymbol.ZModChar

/-! M3: L(1,χ) ≠ 0 for nonprincipal χ (spec §4) -/

namespace Audit.M03

open Complex DirichletCharacter

/-- The nontrivial Dirichlet character mod 4 (proved nontrivial in `Audit/M01.lean`). -/
noncomputable def χ : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

lemma χ_ne_one : χ ≠ 1 := by
  refine (MulChar.ringHomComp_ne_one_iff (Int.castRingHom ℂ).injective_int).mpr fun h ↦ ?_
  have h3 : (1 : MulChar (ZMod 4) ℤ) ((3 : ℕ) : ZMod 4) = -1 :=
    h ▸ ZMod.χ₄_nat_three_mod_four (by norm_num)
  rw [MulChar.one_apply (IsUnit.of_mul_eq_one 3 (by decide))] at h3
  norm_num at h3

#check @DirichletCharacter.LFunction_apply_one_ne_zero
-- ∀ {N : ℕ} {χ : DirichletCharacter ℂ N} [inst : NeZero N],
--   χ ≠ 1 → LFunction χ 1 ≠ 0                                   (χ IMPLICIT)
#check @DirichletCharacter.LFunction_ne_zero_of_re_eq_one
-- ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) [inst : NeZero N] {s : ℂ},
--   s.re = 1 → χ ≠ 1 ∨ s ≠ 1 → LFunction χ s ≠ 0                (χ explicit; hs BEFORE hχs)
#check @DirichletCharacter.LFunction_ne_zero_of_one_le_re
-- ∀ {N : ℕ} (χ : DirichletCharacter ℂ N) [inst : NeZero N] ⦃s : ℂ⦄,
--   χ ≠ 1 ∨ s ≠ 1 → 1 ≤ s.re → LFunction χ s ≠ 0                (χ explicit; ⦃s⦄; hχs BEFORE hs)

example : LFunction χ 1 ≠ 0 :=
  LFunction_apply_one_ne_zero χ_ne_one

example {s : ℂ} (hs : 1 ≤ s.re) : LFunction χ s ≠ 0 :=
  LFunction_ne_zero_of_one_le_re χ (.inl χ_ne_one) hs

end Audit.M03
