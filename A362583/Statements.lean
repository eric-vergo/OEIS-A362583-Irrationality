/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import A362583.Defs
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Real.Irrational

/-!
# A362583: theorem statements (spec §2, §3)

Remaining theorem/lemma targets of the project, with placeholder proofs pending
the proof phases (each tracked in `SORRIES.md`).  Proved targets move to their
layer files with signatures verbatim (lock preserved; see `git tag statement-lock`):
Steps A–B (`bits_infinite_ones`, `bits_infinite_zeros`,
`eventuallyPeriodic_of_not_irrational`) live in `A362583/DigitLayer.lean`.
Statements follow the §3
statement-hygiene principle: elementary `if`/`%` arithmetic, `Nat.primeCounting`,
`Irrational`, and the `Defs.lean` objects only.

Proof architecture (spec §2.2): A (infinitude) → B (rational ⇒ bits eventually
periodic) → C (periodic ⇒ linear race) → D (no linear race) → contradiction.
-/

namespace A362583

/-- **Main analytic theorem** (Step D, spec §2.6): the mod-4 prime race is never
linear — there are no constants `c`, `C` with `|S(N) - c·π(N)| ≤ C` for all `N`,
where `S = raceSum` and `π = Nat.primeCounting` (# primes `≤ N`). -/
theorem raceSum_not_linear :
    ¬ ∃ (c C : ℝ), ∀ N : ℕ, |(raceSum N : ℝ) - c * (Nat.primeCounting N : ℝ)| ≤ C := by
  sorry

/-- **Primary deliverable** (spec §2.2): the A362583 constant is irrational. -/
theorem irrational_x : Irrational x := by
  sorry

/-- Step C (spec §2.5): an eventually periodic bit sequence makes the race sum
linear in the prime count: `raceSum N = c·π(N) + O(1)` with
`c = (P - 2j)/P`, where `j` is the number of ones per period. -/
lemma raceSum_linear_of_eventuallyPeriodic :
    (∃ N P, 0 < P ∧ ∀ k ≥ N, bit (k + P) = bit k) →
    ∃ c C : ℝ, ∀ N : ℕ, |(raceSum N : ℝ) - c * (Nat.primeCounting N : ℝ)| ≤ C := by
  sorry

end A362583
