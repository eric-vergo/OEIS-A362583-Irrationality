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

The primary deliverable `A362583.irrational_ϱ`, assembled from four results, each proved in
its own file:

* `bits_infinite_ones`, `bits_infinite_zeros` (`A362583/DigitLayer.lean`) — Dirichlet's
  theorem at modulus 4 gives infinitely many ones and infinitely many zeros in the bits;
* `eventuallyPeriodic_of_not_irrational` (`A362583/DigitLayer.lean`) — a rational `ϱ` has
  eventually periodic bits;
* `raceSum_linear_of_eventuallyPeriodic` (`A362583/RaceCount.lean`) — eventually periodic
  bits force the race sum onto a linear trajectory `c·π + O(1)`;
* `raceSum_not_linear` (`A362583/CaseZero.lean`) — the race sum is never linear.

Assembly: if `ϱ` were rational, its bits would be eventually periodic, forcing the race sum
to be `c·π + O(1)`, which `raceSum_not_linear` rules out.
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
