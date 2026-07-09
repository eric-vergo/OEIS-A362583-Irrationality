/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
A362583 irrationality blueprint — Definitions chapter.

The four objects of the formalization: the odd primes, their mod-4 bits, the prime race
constant ϱ, and
the Chebyshev race sum. All are stated elementarily (statement hygiene);
the sanity pins of A362583/Pins.lean are described in prose (they are anonymous examples,
so they cannot be lean-linked).
-/

import Verso
import VersoManual
import VersoBlueprint
import Macros
import Bibliography
import A362583.Defs

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true

#doc (Manual) "Definitions" =>

:::group "defs"
The odd primes in order, the mod-4 digit each contributes, the constant they define, and the
Chebyshev race sum.
:::

Everything in this chapter is deliberately elementary: only the $`n`-th-prime function,
remainder arithmetic, if-expressions, finite sums, and a single infinite series appear.
Dirichlet characters, $`L`-functions, and all other analytic objects are confined to proofs
in later chapters, so the statements below — and the irrationality theorem and its analytic
core that reuse them — can be audited without trusting any analytic machinery.

:::definition "def:oddPrime" (lean := "A362583.oddPrime") (parent := "defs")
For $`k \ge 0`, let $`p_k` denote the $`k`-th *odd* prime, so $`p_0 = 3`, $`p_1 = 5`,
$`p_2 = 7`, and so on. In Lean this is the $`(k+1)`-st prime in Mathlib's enumeration
(Nat.nth): since the zeroth prime is $`2`, shifting the index by one skips exactly the prime
$`2`.
:::

:::definition "def:bit" (lean := "A362583.bit") (parent := "defs") (uses := "def:oddPrime")
The $`k`-th *bit* is
$$`b_k = \begin{cases} 1 & \text{if } p_k \equiv 3 \pmod 4, \\ 0 & \text{if } p_k \equiv 1 \pmod 4. \end{cases}`
Every odd prime is congruent to $`1` or $`3` mod $`4`, so the two cases are exhaustive. The
first eight bits are $`1,0,1,1,0,0,1,1` (from the primes $`3, 5, 7, 11, 13, 17, 19, 23`).
:::

:::definition "def:rho" (lean := "A362583.ϱ") (parent := "defs") (uses := "def:bit")
The *prime race constant* $`\varrho` is the sum of the series
$$`\varrho \;=\; \sum_{k \ge 0} \frac{b_k}{2^{\,k+1}} \;=\; 0.7004001\ldots,`
which converges absolutely by comparison with the geometric series. Since each $`b_k` is
$`0` or $`1`, the series is exactly the place-value reading of the binary numeral
$`0.b_0 b_1 b_2 \ldots_2` — and these are genuinely *the* binary digits of $`\varrho`:
infinitely many $`b_k` are $`0` (Dirichlet's theorem), so the digit string is not
eventually all $`1`s and no carry ambiguity arises. Reading successive digit prefixes as
binary integers recovers the OEIS sequence A362583, which is why we call $`\varrho` the
A362583 constant. The theorem of this blueprint is that $`\varrho` is irrational.
:::

:::definition "def:raceSum" (lean := "A362583.raceSum") (parent := "defs")
The *Chebyshev race sum* is the integer
$$`S(N) \;=\; \sum_{\substack{p \le N \\ p \text{ prime}}} \begin{cases} +1 & p \equiv 1 \pmod 4 \\ -1 & p \equiv 3 \pmod 4 \\ \;\;\,0 & p = 2, \end{cases}`
i.e. $`S(N) = \sum_{p \le N} \chi_4(p)` — but stated with plain remainder arithmetic rather
than a character, per the statement-hygiene principle. The convention "primes $`\le N`"
matches Mathlib's prime-counting function $`\pi(N)` (Nat.primeCounting), which the race-sum
theorems quantify against.
:::

Sanity pins guard against definitional drift: the module A362583/Pins.lean proves,
sorry-free, that $`p_0 = 3` and $`p_3 = 11`; that the first eight bits are
$`1,0,1,1,0,0,1,1`; that $`\tfrac12 < \varrho < 1` (strictly — using $`b_0 = 1, b_2 = 1` for the
lower bound and $`b_1 = 0` for strictness above); and that $`S(10) = -1` (from
$`\chi_4(2) = 0`, $`\chi_4(3) = -1`, $`\chi_4(5) = 1`, $`\chi_4(7) = -1`). These pins are
anonymous examples in the Lean source, so they are described here rather than linked. One
further cross-check lives outside Lean: the first 34 bits, read as a binary integer, equal
$`12032782746`, matching the value $`a(35)` in the OEIS b-file for
{citet oeis.a362583}[].

