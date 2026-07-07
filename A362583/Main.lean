/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
import A362583.CaseZero
import A362583.DigitLayer
import A362583.RaceCount

/-!
# A362583 is irrational: final assembly

The primary deliverable: `A362583.irrational_ϱ`, assembled from the four proof
layers, each proved in its own file:

* `bits_infinite_ones`, `bits_infinite_zeros` — Step A, `A362583/DigitLayer.lean`
* `eventuallyPeriodic_of_not_irrational` — Step B, `A362583/DigitLayer.lean`
* `raceSum_linear_of_eventuallyPeriodic` — Step C, `A362583/RaceCount.lean`
* `raceSum_not_linear` — Step D, `A362583/CaseZero.lean`

Assembly: if `ϱ` were rational, its bits would be eventually periodic (Step B,
using Step A), forcing the race sum to be `c·π + O(1)` (Step C), which Step D
rules out.
-/

namespace A362583

/-- **Primary deliverable**: the prime race constant `ϱ = Σ_{k ≥ 0} bₖ · 2^{-(k+1)}` (the
A362583 constant) — the number whose binary expansion is `0.b₀b₁b₂…₂`, where `bₖ = 1` iff
the `k`-th odd prime is `≡ 3 (mod 4)` — is irrational. -/
theorem irrational_ϱ : Irrational ϱ := by
  by_contra h
  exact raceSum_not_linear
    (raceSum_linear_of_eventuallyPeriodic (eventuallyPeriodic_of_not_irrational h))

end A362583
