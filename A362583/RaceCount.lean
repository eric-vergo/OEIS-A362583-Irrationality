/-
Copyright (c) 2026 Eric Vergo. Dedicated to the public domain.
Released under CC0 1.0 Universal as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Prime.Nth
import A362583.Defs

/-!
# A362583: Step C — eventually periodic bits ⇒ linear race

The RACE BOOKKEEPING layer.  If the bit sequence `bit` is eventually periodic
(period `P`, from index `N₀`), then the Chebyshev race sum is linear in the
prime count: `raceSum N = c·π(N) + O(1)` with `c = (P - 2j)/P` (here realized
as `c = W/P` where `W = ∑_{k∈[N₀,N₀+P)} (1 - 2·bit k)` is the exact window sum).

Structure:

* **C1 (bridge)**: `raceSum N = ∑_{k < π(N) - 1} (1 - 2·bit k)` — the filtered
  χ₄-sum over primes `≤ N` reindexed by odd-prime index, by induction on `N`,
  with `Nat.nth_count` supplying the enumeration step.
* **C2 (periodic counting)**: an eventually periodic ±1 sequence has partial
  sums `c·m + O(1)`; crude explicit bound `2·N₀ + 2·P`.
* **C3 (assembly)**: absorb the `m = π(N) - 1` shift (cost `|c| ≤ 1`) into the
  constant, giving `C = 2·N₀ + 2·P + 1`.
-/

namespace A362583

/-! ### C1: the χ₄ summand reindexed by odd-prime index -/

/-- The χ₄ value at a natural number, exactly as it appears in `raceSum` (C1). -/
private def chi (p : ℕ) : ℤ := if p % 4 = 1 then 1 else if p % 4 = 3 then -1 else 0

/-- χ₄ at the `k`-th odd prime through the bit sequence: `1 - 2·bit k ∈ {±1}` (C1). -/
private noncomputable def term (k : ℕ) : ℤ := 1 - 2 * (bit k : ℤ)

/-- The summand `term k = 1 - 2·bit k` is a `±1` value, so `|term k| ≤ 1` (C1). -/
private lemma abs_term_le_one (k : ℕ) : |term k| ≤ 1 := by
  unfold term bit
  split <;> norm_num

/-- Each `oddPrime k` is prime — it is a value of `Nat.nth Nat.Prime` (C1). -/
private lemma oddPrime_prime (k : ℕ) : Nat.Prime (oddPrime k) :=
  Nat.prime_nth_prime (k + 1)

/-- Odd primes exceed `2`: `2 < oddPrime k`, since the index-`0` prime `2` is skipped (C1). -/
private lemma two_lt_oddPrime (k : ℕ) : 2 < oddPrime k := by
  unfold oddPrime
  have h := (Nat.nth_lt_nth Nat.infinite_setOf_prime).mpr k.succ_pos
  rwa [Nat.nth_prime_zero_eq_two] at h

/-- Odd primes are `1` or `3` mod `4` (C1). -/
private lemma oddPrime_mod_four (k : ℕ) : oddPrime k % 4 = 1 ∨ oddPrime k % 4 = 3 := by
  have h2 := two_lt_oddPrime k
  have hodd := (oddPrime_prime k).eq_two_or_odd
  omega

/-- The χ₄ value at the `k`-th odd prime is `1 - 2·bit k` (C1). -/
private lemma chi_oddPrime (k : ℕ) : chi (oddPrime k) = term k := by
  unfold chi term bit
  rcases oddPrime_mod_four k with h | h <;> rw [h] <;> norm_num

/-! ### C1: stepping `raceSum` and `Nat.primeCounting` -/

/-- `raceSum` as an unfiltered range sum, `∑_{p ≤ N} (if p prime then χ₄(p) else 0)` — the
form that steps under `Finset.sum_range_succ` (C1). -/
private lemma raceSum_eq_range_sum (N : ℕ) :
    raceSum N = ∑ p ∈ Finset.range (N + 1), if Nat.Prime p then chi p else 0 := by
  rw [show raceSum N = ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, chi p from rfl,
    Finset.sum_filter]

/-- Stepping the race sum past a prime: `raceSum (n+1) = raceSum n + χ₄(n+1)` (C1). -/
private lemma raceSum_succ_of_prime {n : ℕ} (hp : Nat.Prime (n + 1)) :
    raceSum (n + 1) = raceSum n + chi (n + 1) := by
  rw [raceSum_eq_range_sum (n + 1), raceSum_eq_range_sum n, Finset.sum_range_succ, if_pos hp]

/-- Stepping the race sum past a non-prime leaves it fixed: `raceSum (n+1) = raceSum n` (C1). -/
private lemma raceSum_succ_of_not_prime {n : ℕ} (hp : ¬ Nat.Prime (n + 1)) :
    raceSum (n + 1) = raceSum n := by
  rw [raceSum_eq_range_sum (n + 1), raceSum_eq_range_sum n, Finset.sum_range_succ, if_neg hp,
    add_zero]

/-- The prime count increments at a prime: `π(n+1) = π(n) + 1` (C1). -/
private lemma primeCounting_succ_of_prime {n : ℕ} (hp : Nat.Prime (n + 1)) :
    Nat.primeCounting (n + 1) = Nat.primeCounting n + 1 := by
  change Nat.count Nat.Prime ((n + 1) + 1) = Nat.count Nat.Prime (n + 1) + 1
  rw [Nat.count_succ, if_pos hp]

/-- The prime count is fixed at a non-prime: `π(n+1) = π(n)` (C1). -/
private lemma primeCounting_succ_of_not_prime {n : ℕ} (hp : ¬ Nat.Prime (n + 1)) :
    Nat.primeCounting (n + 1) = Nat.primeCounting n := by
  change Nat.count Nat.Prime ((n + 1) + 1) = Nat.count Nat.Prime (n + 1)
  rw [Nat.count_succ, if_neg hp, add_zero]

/-- **C1, the bridge**: the race sum over primes `≤ N` equals the sum of
`1 - 2·bit k` over the first `π(N) - 1` odd-prime indices.  Natural subtraction
makes the small cases uniform: `π(0) = π(1) = 0`, `π(2) = 1` all give the empty
range, matching `raceSum 0 = raceSum 1 = raceSum 2 = 0` (χ₄(2) = 0). -/
private lemma raceSum_bridge (N : ℕ) :
    raceSum N = ∑ k ∈ Finset.range (Nat.primeCounting N - 1), term k := by
  induction N with
  | zero =>
      have h0 : Nat.primeCounting 0 = 0 := by decide
      rw [h0]
      simp only [Nat.zero_sub, Finset.range_zero, Finset.sum_empty]
      decide
  | succ n ih =>
      by_cases hp : Nat.Prime (n + 1)
      · by_cases h2 : n = 1
        · -- the prime 2 contributes χ₄(2) = 0 and is skipped by the odd-prime index
          subst h2
          have hpi : Nat.primeCounting (1 + 1) = 1 := by decide
          rw [hpi]
          simp only [Nat.sub_self, Finset.range_zero, Finset.sum_empty]
          decide
        · -- n + 1 is an odd prime: both sides gain the same term
          have hn2 : 2 ≤ n := by have := hp.two_le; omega
          have hpos : 1 ≤ Nat.primeCounting n := by
            have hmono : Nat.primeCounting 2 ≤ Nat.primeCounting n :=
              Nat.monotone_primeCounting hn2
            have h21 : Nat.primeCounting 2 = 1 := by decide
            omega
          rw [raceSum_succ_of_prime hp, primeCounting_succ_of_prime hp, ih]
          have hidx : Nat.primeCounting n + 1 - 1 = (Nat.primeCounting n - 1) + 1 := by omega
          rw [hidx, Finset.sum_range_succ]
          congr 1
          have hodd : oddPrime (Nat.primeCounting n - 1) = n + 1 := by
            unfold oddPrime
            have h1 : Nat.primeCounting n - 1 + 1 = Nat.primeCounting n := by omega
            rw [h1]
            exact Nat.nth_count hp
          rw [← hodd, chi_oddPrime]
      · rw [raceSum_succ_of_not_prime hp, primeCounting_succ_of_not_prime hp, ih]

/-! ### C2: partial sums of an eventually periodic ±1 sequence are linear + O(1) -/

/-- Any `n` consecutive `term`s sum to at most `n` in absolute value (C2). -/
private lemma abs_sum_term_le (a n : ℕ) : |∑ k ∈ Finset.range n, term (a + k)| ≤ (n : ℤ) :=
  calc |∑ k ∈ Finset.range n, term (a + k)|
      ≤ ∑ k ∈ Finset.range n, |term (a + k)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k ∈ Finset.range n, 1 := Finset.sum_le_sum fun k _ => abs_term_le_one _
    _ = (n : ℤ) := by simp

/-- Shifting a full window by whole periods does not change its sum (C2). -/
private lemma sum_term_window {N₀ P : ℕ} (hper : ∀ k ≥ N₀, bit (k + P) = bit k) (q : ℕ) :
    ∑ k ∈ Finset.range P, term (N₀ + q * P + k) = ∑ k ∈ Finset.range P, term (N₀ + k) := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [← ih]
      refine Finset.sum_congr rfl fun k _ => ?_
      have harg : N₀ + (q + 1) * P + k = (N₀ + q * P + k) + P := by ring
      rw [harg]
      unfold term
      rw [hper _ (le_trans (Nat.le_add_right _ _) (Nat.le_add_right _ _))]

/-- `q` complete periods contribute exactly `q` window sums (C2). -/
private lemma sum_term_blocks {N₀ P : ℕ} (hper : ∀ k ≥ N₀, bit (k + P) = bit k) (q : ℕ) :
    ∑ k ∈ Finset.range (N₀ + q * P), term k
      = (∑ k ∈ Finset.range N₀, term k)
        + (q : ℤ) * ∑ k ∈ Finset.range P, term (N₀ + k) := by
  induction q with
  | zero => simp
  | succ q ih =>
      have harg : N₀ + (q + 1) * P = (N₀ + q * P) + P := by ring
      rw [harg, Finset.sum_range_add, ih, sum_term_window hper q]
      push_cast
      ring

/-- With `|c| ≤ 1`, scaling a nonnegative real by `c` cannot increase its size:
`|c·t| ≤ t` for `t ≥ 0` (C2 helper, used to bound the `c·(·)` companion of each block). -/
private lemma abs_mul_le_of_abs_le_one {c t : ℝ} (hc1 : |c| ≤ 1) (ht : 0 ≤ t) :
    |c * t| ≤ t := by
  rw [abs_mul, abs_of_nonneg ht]
  exact mul_le_of_le_one_left ht hc1

/-- **C2, short regime** (`m ≤ N₀`): with `|c| ≤ 1`, both the partial sum
`∑_{k<m} term k` and the comparison value `c·m` are at most `m ≤ N₀` in size, so their
difference is at most `2·N₀`. -/
private lemma abs_termSum_sub_short {c : ℝ} (hc1 : |c| ≤ 1) {N₀ m : ℕ} (hm : m ≤ N₀) :
    |((∑ k ∈ Finset.range m, term k : ℤ) : ℝ) - c * (m : ℝ)| ≤ 2 * (N₀ : ℝ) := by
  have hT : |((∑ k ∈ Finset.range m, term k : ℤ) : ℝ)| ≤ (m : ℝ) := by
    have h := abs_sum_term_le 0 m
    simp only [zero_add] at h
    exact_mod_cast h
  have hcm := abs_mul_le_of_abs_le_one hc1 (Nat.cast_nonneg m)
  have hmN : (m : ℝ) ≤ (N₀ : ℝ) := by exact_mod_cast hm
  have htri := abs_sub ((∑ k ∈ Finset.range m, term k : ℤ) : ℝ) (c * (m : ℝ))
  linarith

/-- **C2, long regime** (`N₀ ≤ m`): write `m = N₀ + q·P + r` with `r < P` and split
`[0, m)` into the preperiodic prefix `[0, N₀)`, `q` whole periods, and a partial final
window `[N₀ + q·P, m)`.  Because the slope satisfies `c·P = W` (the window sum), the `q`
complete periods contribute `c·(q·P)` exactly and cancel; only the prefix (size `≤ N₀`)
and the partial window (size `< P`), together with their `c·(·)` companions, remain — total
`≤ 2·N₀ + 2·P`. -/
private lemma abs_termSum_sub_long {N₀ P : ℕ} (hP : 0 < P)
    (hper : ∀ k ≥ N₀, bit (k + P) = bit k) {c : ℝ} (hc1 : |c| ≤ 1)
    (hcP : c * (P : ℝ) = ((∑ k ∈ Finset.range P, term (N₀ + k) : ℤ) : ℝ)) {m : ℕ}
    (hm : N₀ ≤ m) :
    |((∑ k ∈ Finset.range m, term k : ℤ) : ℝ) - c * (m : ℝ)|
      ≤ 2 * (N₀ : ℝ) + 2 * (P : ℝ) := by
  obtain ⟨q, r, hrP, hm_eq⟩ : ∃ q r, r < P ∧ m = N₀ + q * P + r := by
    refine ⟨(m - N₀) / P, (m - N₀) % P, Nat.mod_lt _ hP, ?_⟩
    have h1 : N₀ + (P * ((m - N₀) / P) + (m - N₀) % P) = m := by
      rw [Nat.div_add_mod]
      exact Nat.add_sub_cancel' hm
    calc m = N₀ + (P * ((m - N₀) / P) + (m - N₀) % P) := h1.symm
      _ = N₀ + (m - N₀) / P * P + (m - N₀) % P := by ring
  have hsplitZ : (∑ k ∈ Finset.range m, term k)
      = (∑ k ∈ Finset.range N₀, term k)
        + (q : ℤ) * (∑ k ∈ Finset.range P, term (N₀ + k))
        + ∑ k ∈ Finset.range r, term (N₀ + q * P + k) := by
    rw [hm_eq, Finset.sum_range_add, sum_term_blocks hper q]
  have hsplit : ((∑ k ∈ Finset.range m, term k : ℤ) : ℝ)
      = ((∑ k ∈ Finset.range N₀, term k : ℤ) : ℝ)
        + (q : ℝ) * ((∑ k ∈ Finset.range P, term (N₀ + k) : ℤ) : ℝ)
        + ((∑ k ∈ Finset.range r, term (N₀ + q * P + k) : ℤ) : ℝ) := by
    exact_mod_cast hsplitZ
  have hA : |((∑ k ∈ Finset.range N₀, term k : ℤ) : ℝ)| ≤ (N₀ : ℝ) := by
    have h := abs_sum_term_le 0 N₀
    simp only [zero_add] at h
    exact_mod_cast h
  have hB : |((∑ k ∈ Finset.range r, term (N₀ + q * P + k) : ℤ) : ℝ)| ≤ (r : ℝ) := by
    exact_mod_cast abs_sum_term_le (N₀ + q * P) r
  have hm_cast : (m : ℝ) = (N₀ : ℝ) + (q : ℝ) * (P : ℝ) + (r : ℝ) := by
    rw [hm_eq]
    push_cast
    ring
  have hkey : ((∑ k ∈ Finset.range m, term k : ℤ) : ℝ) - c * (m : ℝ)
      = (((∑ k ∈ Finset.range N₀, term k : ℤ) : ℝ) - c * (N₀ : ℝ))
        + (((∑ k ∈ Finset.range r, term (N₀ + q * P + k) : ℤ) : ℝ) - c * (r : ℝ)) := by
    rw [hsplit, hm_cast, ← hcP]
    ring
  have hcN := abs_mul_le_of_abs_le_one hc1 (Nat.cast_nonneg N₀)
  have hcr := abs_mul_le_of_abs_le_one hc1 (Nat.cast_nonneg r)
  have hrP' : (r : ℝ) ≤ (P : ℝ) := by exact_mod_cast hrP.le
  calc |((∑ k ∈ Finset.range m, term k : ℤ) : ℝ) - c * (m : ℝ)|
      = |(((∑ k ∈ Finset.range N₀, term k : ℤ) : ℝ) - c * (N₀ : ℝ))
          + (((∑ k ∈ Finset.range r, term (N₀ + q * P + k) : ℤ) : ℝ) - c * (r : ℝ))| := by
        rw [hkey]
    _ ≤ |((∑ k ∈ Finset.range N₀, term k : ℤ) : ℝ) - c * (N₀ : ℝ)|
          + |((∑ k ∈ Finset.range r, term (N₀ + q * P + k) : ℤ) : ℝ) - c * (r : ℝ)| :=
        abs_add_le _ _
    _ ≤ (|((∑ k ∈ Finset.range N₀, term k : ℤ) : ℝ)| + |c * (N₀ : ℝ)|)
          + (|((∑ k ∈ Finset.range r, term (N₀ + q * P + k) : ℤ) : ℝ)| + |c * (r : ℝ)|) :=
        add_le_add (abs_sub _ _) (abs_sub _ _)
    _ ≤ 2 * (N₀ : ℝ) + 2 * (P : ℝ) := by linarith

/-- **C2**: with `c = W/P` (window sum over period), the `term`-partial sums track `c·m`
within the generous constant `2·N₀ + 2·P`.  Only a weakest-sufficient bound is needed, so
the two regimes `m ≤ N₀` and `N₀ ≤ m` are dispatched to the crude block bounds
`abs_termSum_sub_short` / `abs_termSum_sub_long`. -/
private lemma exists_c_bound {N₀ P : ℕ} (hP : 0 < P)
    (hper : ∀ k ≥ N₀, bit (k + P) = bit k) :
    ∃ c : ℝ, |c| ≤ 1 ∧ ∀ m : ℕ,
      |((∑ k ∈ Finset.range m, term k : ℤ) : ℝ) - c * (m : ℝ)|
        ≤ 2 * (N₀ : ℝ) + 2 * (P : ℝ) := by
  have hPpos : (0 : ℝ) < (P : ℝ) := by exact_mod_cast hP
  have hP0 : (P : ℝ) ≠ 0 := ne_of_gt hPpos
  obtain ⟨c, hc_def⟩ :
      ∃ c : ℝ, c = ((∑ k ∈ Finset.range P, term (N₀ + k) : ℤ) : ℝ) / (P : ℝ) := ⟨_, rfl⟩
  have hWle : |((∑ k ∈ Finset.range P, term (N₀ + k) : ℤ) : ℝ)| ≤ (P : ℝ) := by
    exact_mod_cast abs_sum_term_le N₀ P
  have hc1 : |c| ≤ 1 := by
    rw [hc_def, abs_div, Nat.abs_cast]
    exact (div_le_one hPpos).mpr hWle
  have hcP : c * (P : ℝ) = ((∑ k ∈ Finset.range P, term (N₀ + k) : ℤ) : ℝ) := by
    rw [hc_def]
    exact div_mul_cancel₀ _ hP0
  refine ⟨c, hc1, fun m => ?_⟩
  rcases lt_or_ge m N₀ with hm | hm
  · exact (abs_termSum_sub_short hc1 hm.le).trans (le_add_of_nonneg_right (by positivity))
  · exact abs_termSum_sub_long hP hper hc1 hcP hm

/-! ### C3: assembly -/

/-- **Step C**: an eventually periodic bit sequence makes
the race sum linear in the prime count, `raceSum N = c·π(N) + O(1)`.  The slope
is `c = W/P` for the exact window sum `W = ∑_{k∈[N₀,N₀+P)} (1 - 2·bit k) = P - 2j`,
and the constant `C = 2·N₀ + 2·P + 1` absorbs the `m = π(N) - 1` reindexing
via `|c| ≤ 1` (all-ones/all-zeros patterns are just `c = ∓1`, no separate case). -/
lemma raceSum_linear_of_eventuallyPeriodic :
    (∃ N P, 0 < P ∧ ∀ k ≥ N, bit (k + P) = bit k) →
    ∃ c C : ℝ, ∀ N : ℕ, |(raceSum N : ℝ) - c * (Nat.primeCounting N : ℝ)| ≤ C := by
  rintro ⟨N₀, P, hP, hper⟩
  obtain ⟨c, hc1, hc⟩ := exists_c_bound hP hper
  refine ⟨c, 2 * (N₀ : ℝ) + 2 * (P : ℝ) + 1, fun N => ?_⟩
  rw [raceSum_bridge N]
  rcases Nat.eq_zero_or_pos (Nat.primeCounting N) with h0 | hpos
  · -- π(N) = 0 (N ∈ {0, 1}): both sides vanish
    rw [h0]
    simp only [Nat.zero_sub, Finset.range_zero, Finset.sum_empty, Int.cast_zero,
      Nat.cast_zero, mul_zero, sub_zero, abs_zero]
    have h1 : (0 : ℝ) ≤ (N₀ : ℝ) := Nat.cast_nonneg N₀
    have h2 : (0 : ℝ) ≤ (P : ℝ) := Nat.cast_nonneg P
    linarith
  · -- π(N) ≥ 1: shift by one index, absorbing |c| ≤ 1 into the constant
    have hsucc : (Nat.primeCounting N : ℝ) = ((Nat.primeCounting N - 1 : ℕ) : ℝ) + 1 := by
      have h1 : Nat.primeCounting N - 1 + 1 = Nat.primeCounting N := by omega
      exact_mod_cast h1.symm
    rw [hsucc]
    have hkey : ((∑ k ∈ Finset.range (Nat.primeCounting N - 1), term k : ℤ) : ℝ)
          - c * (((Nat.primeCounting N - 1 : ℕ) : ℝ) + 1)
        = (((∑ k ∈ Finset.range (Nat.primeCounting N - 1), term k : ℤ) : ℝ)
            - c * ((Nat.primeCounting N - 1 : ℕ) : ℝ)) - c := by ring
    rw [hkey]
    have h1 := hc (Nat.primeCounting N - 1)
    have htri := abs_sub
      (((∑ k ∈ Finset.range (Nat.primeCounting N - 1), term k : ℤ) : ℝ)
        - c * ((Nat.primeCounting N - 1 : ℕ) : ℝ)) c
    linarith

end A362583
