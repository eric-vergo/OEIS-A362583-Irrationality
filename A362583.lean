/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
import A362583.BoundedHolo
import A362583.CaseNonzero
import A362583.CaseZero
import A362583.Character
import A362583.Defs
import A362583.DigitLayer
import A362583.Divergence
import A362583.EulerLog
import A362583.Layers
import A362583.Main
import A362583.Pins
import A362583.RaceCount

/-!
# A362583 irrationality: library root

Root module for the `A362583` library, importing every module of the
`sorry`-free proof that the prime race constant `ϱ` (the A362583 constant)
is irrational.

The primary deliverable is `A362583.irrational_ϱ` (`A362583/Main.lean`).  The
elementary definitions live in `A362583/Defs.lean`; the proof combines three
ingredients:

* the digit layer (`A362583/DigitLayer.lean`) — Dirichlet's theorem at modulus 4
  puts infinitely many primes in each class `1, 3 (mod 4)`, and the binary digits
  of a rational are eventually periodic;
* the race bookkeeping (`A362583/RaceCount.lean`) — eventually periodic digits force
  the Chebyshev race sum onto a linear trajectory `c·π(N) + O(1)`;
* the analytic non-linearity of the race sum (`A362583/Character.lean`,
  `A362583/Divergence.lean`, `A362583/Layers.lean`, `A362583/EulerLog.lean`,
  `A362583/BoundedHolo.lean`, `A362583/CaseNonzero.lean`, `A362583/CaseZero.lean`) —
  the theorem `raceSum_not_linear`, obtained from the Dirichlet `L`-function `L(χ, ·)`
  and the divergence of `Σ 1/p`.

See the module docstring of each file for details.
-/
