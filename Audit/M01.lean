import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Data.Complex.Basic

/-! M1: χ₄ as a character; value lemmas; bridge to ℂ (spec §4) -/

namespace Audit.M01

-- The ℤ-valued quadratic character mod 4 and its value lemmas:
#check @ZMod.χ₄
-- ZMod.χ₄ : MulChar (ZMod 4) ℤ
#check @ZMod.χ₄_nat_eq_if_mod_four
-- ∀ (n : ℕ), ZMod.χ₄ ↑n = if n % 2 = 0 then 0 else if n % 4 = 1 then 1 else -1
#check @ZMod.χ₄_nat_one_mod_four
-- ∀ {n : ℕ}, n % 4 = 1 → ZMod.χ₄ ↑n = 1
#check @ZMod.χ₄_nat_three_mod_four
-- ∀ {n : ℕ}, n % 4 = 3 → ZMod.χ₄ ↑n = -1

/-- The nontrivial Dirichlet character mod 4, ℂ-valued: `ZMod.χ₄` pushed along `ℤ →+* ℂ`. -/
noncomputable def χ : DirichletCharacter ℂ 4 :=
  ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)

/-- `χ₄ ≠ 1`: they differ at `3` (a unit of `ZMod 4`), where `χ₄` is `-1` but `1` is `1`. -/
lemma χ₄_ne_one : (ZMod.χ₄ : MulChar (ZMod 4) ℤ) ≠ 1 := by
  intro h
  have h3 : (1 : MulChar (ZMod 4) ℤ) ((3 : ℕ) : ZMod 4) = -1 :=
    h ▸ ZMod.χ₄_nat_three_mod_four (by norm_num)
  rw [MulChar.one_apply (IsUnit.of_mul_eq_one 3 (by decide))] at h3
  norm_num at h3

/-- Nontriviality transfers to ℂ since `ℤ →+* ℂ` is injective.
NB: `isUnit_of_mul_eq_one` was renamed `IsUnit.of_mul_eq_one` in this Mathlib;
`Int.cast_injective` also works in place of `RingHom.injective_int`. -/
lemma χ_ne_one : χ ≠ 1 :=
  (MulChar.ringHomComp_ne_one_iff (Int.castRingHom ℂ).injective_int).mpr χ₄_ne_one

/-- Value lemma in the shape we need downstream: `χ` is `-1` on `3 mod 4`. -/
lemma χ_nat_three : χ ((3 : ℕ) : ZMod 4) = -1 := by
  unfold χ
  rw [MulChar.ringHomComp_apply, ZMod.χ₄_nat_three_mod_four (by norm_num)]
  norm_num

end Audit.M01
