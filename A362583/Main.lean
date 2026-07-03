/-
Copyright (c) 2026 Eric Vergo. Dedicated to the public domain.
Released under CC0 1.0 Universal as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
import A362583.CaseZero
import A362583.DigitLayer
import A362583.RaceCount

/-!
# A362583 is irrational (spec §2.7, assembly)

The primary deliverable: `A362583.irrational_x`.  The locked theorem/lemma
statements are proved in their layer files, signatures verbatim from the
Phase-1 statement lock (`git tag statement-lock`):

* `bits_infinite_ones`, `bits_infinite_zeros` — Step A, `A362583/DigitLayer.lean`
* `eventuallyPeriodic_of_not_irrational` — Step B, `A362583/DigitLayer.lean`
* `raceSum_linear_of_eventuallyPeriodic` — Step C, `A362583/RaceCount.lean`
* `raceSum_not_linear` — Step D, `A362583/CaseZero.lean`

Assembly (§2.2, §2.7): if `x` were rational, its bits would be eventually
periodic (Step B, using Step A), forcing the race sum to be `c·π + O(1)`
(Step C), which Step D rules out.
-/

namespace A362583

/-- **Primary deliverable** (spec §2.2, §2.7): the A362583 constant
`x = 0.b₀b₁b₂…` in binary — where `bₖ = 1` iff the `k`-th odd prime is
`≡ 3 (mod 4)` — is irrational. -/
theorem irrational_x : Irrational x := by
  by_contra h
  exact raceSum_not_linear
    (raceSum_linear_of_eventuallyPeriodic (eventuallyPeriodic_of_not_irrational h))

end A362583
