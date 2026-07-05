/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A362583: definitions

The four objects of the formalization, stated elementarily so that the
statements are auditable by a reader who trusts only Mathlib: only `Nat.nth`,
`%`-arithmetic, `if`-expressions, finite sums and a `tsum` appear here.  The
heavier machinery — `ZMod.χ₄`, `DirichletCharacter`, `LFunction` and friends —
is confined to proofs, never to statements.

* `A362583.oddPrime k` — the `k`-th odd prime (`oddPrime 0 = 3`); the `p_{k+1}`
  of the 1-based enumeration of odd primes.
* `A362583.bit k` — the `k`-th binary digit of the constant.
* `A362583.ϱ` — the prime race constant `ϱ = 0.b₀b₁b₂…₂ ≈ 0.7004001…`, the OEIS
  A362583 constant.
* `A362583.raceSum N` — the Chebyshev race sum `S(N) = Σ_{p ≤ N} χ₄(p)`.
-/

namespace A362583

/-- The `k`-th odd prime: `oddPrime 0 = 3`, `oddPrime 1 = 5`, `oddPrime 2 = 7`, ….
Writing the odd primes as `p_1, p_2, …`, this is `p_{k+1}`; since
`Nat.nth Nat.Prime 0 = 2`, skipping index 0 skips exactly the prime 2. -/
noncomputable def oddPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k + 1)

/-- `k`-th bit of the constant: `1` iff the `k`-th odd prime is `≡ 3 (mod 4)`.
The `b_{k+1}` of the 1-based bit sequence; first values `1 0 1 1 0 0 1 1`
(primes `3, 5, 7, 11, 13, 17, 19, 23`). -/
noncomputable def bit (k : ℕ) : ℕ := if oddPrime k % 4 = 3 then 1 else 0

/-- The prime race constant `ϱ = 0.b₀b₁b₂…₂ ≈ 0.7004001…` (the OEIS A362583
constant), the real number whose `k`-th binary digit is `bit k`:
`ϱ = Σ_{k ≥ 0} bit k · 2^{-(k+1)}`. -/
noncomputable def ϱ : ℝ := ∑' k : ℕ, (bit k : ℝ) / 2 ^ (k + 1)

/-- Chebyshev race sum `S(N) = Σ_{p ≤ N} χ₄(p)`, stated elementarily:
`+1` for primes `≡ 1 (mod 4)`, `-1` for primes `≡ 3 (mod 4)`, `0` for `p = 2`.
The range `Finset.range (N + 1)` means primes `≤ N`, matching the convention of
`Nat.primeCounting N` (# primes `≤ N`). -/
def raceSum (N : ℕ) : ℤ :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
    (if p % 4 = 1 then 1 else if p % 4 = 3 then -1 else 0)

end A362583
