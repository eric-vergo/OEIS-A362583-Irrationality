/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
import Mathlib.Data.Nat.Nth
import Mathlib.NumberTheory.Real.Irrational

/-!
# Comparator challenge: the A362583 claim, stated independently

This module is the **comparator challenge**: an independent, auditable
statement of exactly what this project claims to prove.  It intentionally
imports nothing from the `A362583` library — the three definitions are copied
verbatim from `A362583/Defs.lean` and the main theorem statement from
`A362583/Main.lean`, here left with proof `sorry`.

The `sorry` is **by design**: this file is the comparator's *input*, not part of
any proof.  Its companion, the `Solution` module (`comparator/Solution.lean`),
re-states the same definitions and *proves* this theorem, deriving it from the
library's `A362583.irrational_ϱ`.  The comparator (`leanprover/comparator`;
Linux-only, run in CI — see `comparator.json` and `comparator-status.json`)
elaborates this challenge module and the `Solution` module in separate
environments and certifies, kernel-checked, that the solution proves this exact
statement — `Challenge.irrational_ϱ` — using only the permitted axioms
`propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Challenge

/-- The `k`-th odd prime: `oddPrime 0 = 3`, `oddPrime 1 = 5`, `oddPrime 2 = 7`, ….
Writing the odd primes as `p_1, p_2, …`, this is `p_{k+1}`; since
`Nat.nth Nat.Prime 0 = 2`, skipping index 0 skips exactly the prime 2. -/
noncomputable def oddPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k + 1)

/-- `k`-th bit of the constant: `1` iff the `k`-th odd prime is `≡ 3 (mod 4)`.
The `b_{k+1}` of the 1-based bit sequence; first values `1 0 1 1 0 0 1 1`
(primes `3, 5, 7, 11, 13, 17, 19, 23`). -/
noncomputable def bit (k : ℕ) : ℕ := if oddPrime k % 4 = 3 then 1 else 0

/-- The prime race constant (the A362583 constant): the sum of the series
`ϱ = Σ_{k ≥ 0} bit k · 2^{-(k+1)}`, i.e. the real number whose `k`-th binary digit is
`bit k` — in binary `0.b₀b₁b₂…₂ ≈ 0.7004001…` (decimal). OEIS A362583 lists the
successive digit prefixes read as binary integers. -/
noncomputable def ϱ : ℝ := ∑' k : ℕ, (bit k : ℝ) / 2 ^ (k + 1)

/-- **Primary deliverable**: the prime race constant `ϱ = Σ_{k ≥ 0} bₖ · 2^{-(k+1)}` (the
A362583 constant) — the number whose binary expansion is `0.b₀b₁b₂…₂`, where `bₖ = 1` iff
the `k`-th odd prime is `≡ 3 (mod 4)` — is irrational. -/
theorem irrational_ϱ : Irrational ϱ := sorry

end Challenge
