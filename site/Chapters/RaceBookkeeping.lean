/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
A362583 irrationality blueprint — Race Bookkeeping chapter.

Eventually periodic bits force the race sum onto a linear trajectory
S(N) = c·π(N) + O(1) with rational slope c = (P − 2j)/P.
-/

import Verso
import VersoManual
import VersoBlueprint
import Macros
import Bibliography
import A362583.RaceCount

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true

#doc (Manual) "Race Bookkeeping" =>

:::group "race"
Eventually periodic bits make the Chebyshev race sum linear in the prime count, up to a
bounded error.
:::

This chapter is pure bookkeeping — no analysis, no characters. Its single theorem converts
the eventual periodicity of the bits into the statement the analytic core will refute: a
linear race $`S(N) = c\,\pi(N) + O(1)`.

:::theorem "thm:race-linear" (lean := "A362583.raceSum_linear_of_eventuallyPeriodic") (parent := "race") (uses := "def:raceSum, def:bit")
If the bit sequence is eventually periodic — $`b_{k+P} = b_k` for all
$`k \ge N_0`, with $`P > 0` — then there are constants $`c \in \mathbb{R}` and $`C` with
$$`\bigl|\, S(N) - c\,\pi(N) \,\bigr| \;\le\; C \qquad \text{for all } N.`
The slope produced by the proof is rational: $`c = (P - 2j)/P \in [-1,1] \cap \Q`, where
$`j` is the number of ones among $`b_{N_0}, \ldots, b_{N_0+P-1}`.
:::

:::proof "thm:race-linear"
The bridge between the race sum and the bits: the prime $`2` contributes $`0` to $`S(N)`, and
the $`k`-th odd prime contributes $`\chi_4(p_k) = 1 - 2 b_k` ($`+1` for a zero bit, $`-1` for
a one bit). For $`N \ge 2` there are exactly $`\pi(N) - 1` odd primes $`\le N`, so
$$`S(N) \;=\; \sum_{k < \pi(N) - 1} (1 - 2 b_k):`
the race sum is a partial sum of the $`\pm 1` sequence read off the bits. (Translating
between "the $`k`-th odd prime" and "primes $`\le N`" is Mathlib's Galois connection between
the $`n`-th-prime function and the prime-counting function.)

Now count over the periodic structure. Each full period window of length $`P` contributes the
same window sum $`W = \sum_{k \in [N_0, N_0 + P)} (1 - 2 b_k) = P - 2j`, so setting
$`c := W / P`, the partial sums over $`m` terms deviate from $`c\,m` by a bounded amount: the
preperiodic prefix contributes at most $`2 N_0`, the incomplete final window at most $`2P`,
and each complete window deviates from $`cP` by exactly $`0`. Since $`|1 - 2b_k| = 1` we get
$`|c| \le 1`, and reindexing $`m = \pi(N) - 1` costs one more $`|c|`, absorbed into the final
constant $`C = 2 N_0 + 2 P + 1`. The all-ones and all-zeros patterns are simply $`c = -1` and
$`c = +1`; no separate case is needed. $`\blacksquare`
:::
