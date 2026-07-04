/-
Copyright (c) 2026 Eric Vergo. Dedicated to the public domain.
Released under CC0 1.0 Universal as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
import A362583.Defs
import Mathlib.Data.Nat.Prime.Nth

/-!
# A362583: sanity pins

Proved checks that the `Defs.lean` objects mean what they are intended to mean:
the indexing of `oddPrime`, the first eight bits (primes `3,5,7,11,13,17,19,23`
give `1 0 1 1 0 0 1 1`), the bracketing `1/2 < x < 1`, and `raceSum 10 = -1`
(`χ₄(2) = 0, χ₄(3) = -1, χ₄(5) = 1, χ₄(7) = -1`).

The helper lemmas are `private`: they exist only to state these pins.  The API
that the proof proper uses is developed in the layer files.
-/

namespace A362583

/-! ## Small values of `oddPrime` and `bit` -/

/-- `Nat.nth Nat.Prime` pin via the `nth`/`count` Galois connection:
`Nat.count Nat.Prime m` evaluates by `decide` for small `m`. -/
private lemma oddPrime_eq_of_count {k m : ℕ} (hm : Nat.Prime m)
    (h : Nat.count Nat.Prime m = k + 1) : oddPrime k = m := by
  unfold oddPrime
  exact h ▸ Nat.nth_count hm

private lemma oddPrime_zero : oddPrime 0 = 3 := oddPrime_eq_of_count (by decide) (by decide)
private lemma oddPrime_one : oddPrime 1 = 5 := oddPrime_eq_of_count (by decide) (by decide)
private lemma oddPrime_two : oddPrime 2 = 7 := oddPrime_eq_of_count (by decide) (by decide)
private lemma oddPrime_three : oddPrime 3 = 11 := oddPrime_eq_of_count (by decide) (by decide)
private lemma oddPrime_four : oddPrime 4 = 13 := oddPrime_eq_of_count (by decide) (by decide)
private lemma oddPrime_five : oddPrime 5 = 17 := oddPrime_eq_of_count (by decide) (by decide)
private lemma oddPrime_six : oddPrime 6 = 19 := oddPrime_eq_of_count (by decide) (by decide)
private lemma oddPrime_seven : oddPrime 7 = 23 := oddPrime_eq_of_count (by decide) (by decide)

private lemma bit_zero : bit 0 = 1 := by simp [bit, oddPrime_zero]
private lemma bit_one : bit 1 = 0 := by simp [bit, oddPrime_one]
private lemma bit_two : bit 2 = 1 := by simp [bit, oddPrime_two]
private lemma bit_three : bit 3 = 1 := by simp [bit, oddPrime_three]
private lemma bit_four : bit 4 = 0 := by simp [bit, oddPrime_four]
private lemma bit_five : bit 5 = 0 := by simp [bit, oddPrime_five]
private lemma bit_six : bit 6 = 1 := by simp [bit, oddPrime_six]
private lemma bit_seven : bit 7 = 1 := by simp [bit, oddPrime_seven]

/-! ## The pins -/

example : oddPrime 0 = 3 := oddPrime_zero

example : oddPrime 3 = 11 := oddPrime_three

example : bit 0 = 1 ∧ bit 1 = 0 ∧ bit 2 = 1 ∧ bit 3 = 1 ∧
    bit 4 = 0 ∧ bit 5 = 0 ∧ bit 6 = 1 ∧ bit 7 = 1 :=
  ⟨bit_zero, bit_one, bit_two, bit_three, bit_four, bit_five, bit_six, bit_seven⟩

/-- `b₀ = 1` gives `x > 1/2` (indeed `x ≥ 5/8` using `b₂ = 1`); `b₁ = 0` gives
`x < 1` strictly. Comparison series: the geometric `∑' k, (1/2)^(k+1) = 1`. -/
example : (1:ℝ)/2 < x ∧ x < 1 := by
  have hx : x = ∑' k : ℕ, (bit k : ℝ) / 2 ^ (k + 1) := rfl
  -- bits are 0/1, so terms are nonnegative and dominated by the geometric series
  have hb : ∀ k, bit k ≤ 1 := by
    intro k
    unfold bit
    split <;> omega
  have hnonneg : ∀ k : ℕ, 0 ≤ (bit k : ℝ) / 2 ^ (k + 1) := by
    intro k
    positivity
  have hle : ∀ k : ℕ, (bit k : ℝ) / 2 ^ (k + 1) ≤ ((1:ℝ)/2) ^ (k + 1) := by
    intro k
    rw [div_pow, one_pow]
    gcongr
    exact_mod_cast hb k
  have hg : Summable (fun k : ℕ => ((1:ℝ)/2) ^ (k + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (by norm_num) (by norm_num))
  have hf : Summable (fun k : ℕ => (bit k : ℝ) / 2 ^ (k + 1)) :=
    Summable.of_nonneg_of_le hnonneg hle hg
  have hgsum : ∑' k : ℕ, ((1:ℝ)/2) ^ (k + 1) = 1 := by
    simp only [pow_succ]
    rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    norm_num
  constructor
  · -- 1/2 < 5/8 = b₀/2 + b₁/4 + b₂/8 ≤ x
    have hpart : ∑ k ∈ Finset.range 3, (bit k : ℝ) / 2 ^ (k + 1) = 5/8 := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      rw [bit_zero, bit_one, bit_two]
      norm_num
    calc (1:ℝ)/2 < 5/8 := by norm_num
      _ = ∑ k ∈ Finset.range 3, (bit k : ℝ) / 2 ^ (k + 1) := hpart.symm
      _ ≤ ∑' k : ℕ, (bit k : ℝ) / 2 ^ (k + 1) :=
          hf.sum_le_tsum (Finset.range 3) fun i _ => hnonneg i
      _ = x := hx.symm
  · -- strict at k = 1: b₁ = 0, so the k = 1 term is < the geometric term
    have h1 : (bit 1 : ℝ) / 2 ^ (1 + 1) < ((1:ℝ)/2) ^ (1 + 1) := by
      rw [bit_one]
      norm_num
    calc x < ∑' k : ℕ, ((1:ℝ)/2) ^ (k + 1) := by
          rw [hx]
          exact Summable.tsum_lt_tsum_of_nonneg hnonneg hle h1 hg
      _ = 1 := hgsum

example : raceSum 10 = -1 := by decide

end A362583
