import Mathlib.NumberTheory.LSeries.PrimesInAP

/-! M6: Dirichlet — infinitude of primes in residue classes mod 4 (spec §4) -/

#check @Nat.infinite_setOf_prime_and_eq_mod
-- {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) :
--   {p : ℕ | p.Prime ∧ (p : ZMod q) = a}.Infinite

#check @Nat.forall_exists_prime_gt_and_eq_mod
-- (ha : IsUnit a) (n : ℕ) : ∃ p > n, p.Prime ∧ (p : ZMod q) = a

-- Class p ≡ 1 (mod 4):
example : {p : ℕ | p.Prime ∧ (p : ZMod 4) = 1}.Infinite :=
  Nat.infinite_setOf_prime_and_eq_mod isUnit_one

-- Class p ≡ 3 (mod 4); `IsUnit (3 : ZMod 4)` via an explicit unit (3·3 = 9 = 1).
-- (`by decide` also works — a DecidablePred IsUnit instance is available.)
example : {p : ℕ | p.Prime ∧ (p : ZMod 4) = 3}.Infinite :=
  Nat.infinite_setOf_prime_and_eq_mod ⟨⟨3, 3, by decide, by decide⟩, rfl⟩

-- Bridge `(p : ZMod 4) = a` ↔ `p % 4 = a` (needed project-wide):
-- rewrite the ZMod literal as a ℕ-cast, then `ZMod.natCast_eq_natCast_iff'`.
example (p : ℕ) : (p : ZMod 4) = 3 ↔ p % 4 = 3 := by
  rw [← Nat.cast_ofNat (R := ZMod 4) (n := 3), ZMod.natCast_eq_natCast_iff']

example (p : ℕ) : (p : ZMod 4) = 1 ↔ p % 4 = 1 := by
  rw [← Nat.cast_one (R := ZMod 4), ZMod.natCast_eq_natCast_iff']

-- `≡ [MOD]` variant, for when `Nat.ModEq` is the preferred interface:
#check @ZMod.natCast_eq_natCast_iff
-- (a b c : ℕ) : (a : ZMod c) = b ↔ a ≡ b [MOD c]
