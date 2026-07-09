/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
import A362583

/-!
# Comparator solution: proving the challenge statement

This module is the **official solution** to the comparator challenge
(`Challenge/Challenge.lean`).  It re-states the three definitions verbatim and
*proves* the challenge theorem `Challenge.irrational_ϱ`, deriving it from the
`A362583` library's `A362583.irrational_ϱ`.

The comparator (`leanprover/comparator`; see `comparator.json`) loads this
module and the challenge module in **separate** environments, so this file must
not import `Challenge`: the three definitions below are byte-identical copies of
the challenge's (and hence of `A362583/Defs.lean`).  That makes each
`Challenge.*` constant definitionally identical across the two environments, so
the comparator can confirm statement equality and kernel-replay the proof.
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

/-- The challenge's constant is the library's `A362583.ϱ`: the two are
definitionally equal because the `oddPrime`, `bit`, `ϱ` definitions above are
byte-identical copies of the library's. -/
theorem ϱ_eq : ϱ = A362583.ϱ := rfl

/-- **Solution to the comparator challenge**: the challenge statement
`Irrational Challenge.ϱ`, proved by transporting the library's
`A362583.irrational_ϱ` across `ϱ_eq`. -/
theorem irrational_ϱ : Irrational ϱ := ϱ_eq ▸ A362583.irrational_ϱ

end Challenge
