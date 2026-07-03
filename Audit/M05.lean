import Mathlib.NumberTheory.SumPrimeReciprocals

/-! M5: divergence of Σ 1/p over primes (spec §4) -/

-- Main form, indexed by the subtype `Nat.Primes`:
#check @Nat.Primes.not_summable_one_div
-- ¬ Summable (fun p : Nat.Primes ↦ (1 / p : ℝ))

-- Indicator-on-ℕ form (sub-sum of the harmonic series):
#check @not_summable_one_div_on_primes
-- ¬ Summable (Set.indicator {p | p.Prime} fun n : ℕ ↦ (1 : ℝ) / n)

-- Sharp threshold: Σ p^r converges iff r < -1:
#check @Nat.Primes.summable_rpow
-- ∀ {r : ℝ}, Summable (fun p : Nat.Primes ↦ (p : ℝ) ^ r) ↔ r < -1

example : ¬ Summable (fun p : Nat.Primes ↦ (1 / p : ℝ)) :=
  Nat.Primes.not_summable_one_div
