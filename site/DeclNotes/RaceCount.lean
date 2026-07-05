/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
A362583 irrationality blueprint — declaration notes for the Race Bookkeeping helpers.

Authored sidecar prose (`:::declNotes`) for the private helper declarations of
A362583/RaceCount.lean (Step C, the race bookkeeping) that no blueprint node wires.
Each block is keyed by the full declaration name and surfaces on that declaration's
page as its informal-statement cell (in preference to the docstring). The blocks
render nothing inline, so this document itself renders as a near-empty page.
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

#doc (Manual) "Declaration notes: RaceCount" =>

:::declNotes "A362583.chi"
`chi p` is the integer that is $`+1` when $`p \equiv 1 \pmod 4`, $`-1` when
$`p \equiv 3 \pmod 4`, and $`0` in every other case — in particular at $`p = 2` and at
even arguments. It is the plain-remainder-arithmetic form of the mod-$`4` character
$`\chi_4(p)` exactly as it sits inside `raceSum`, written with nested if-tests rather
than a Dirichlet character.

This is the summand of the race sum before any reindexing: `raceSum_bridge` rewrites
$`S(N)` as a range sum of `chi`, and `chi_oddPrime` then identifies its value at each
odd prime with the bit term $`1 - 2 b_k`.
:::

:::declNotes "A362583.term"
`term k` is the integer $`t_k = 1 - 2 b_k`, i.e. $`+1` when the $`k`-th bit is $`0` and
$`-1` when it is $`1`. It is the $`\pm 1` value the $`k`-th odd prime contributes to the
race, read directly off the bit sequence rather than off the prime.

The whole of Step C works with partial sums $`\sum_{k < m} t_k`: the bridge shows $`S(N)`
equals such a partial sum over the first $`\pi(N) - 1` odd-prime indices, and the C2
lemmas bound how far those partial sums stray from a straight line.
:::

:::declNotes "A362583.abs_term_le_one"
Every summand is bounded in size by one: $`|t_k| \le 1` (in fact $`t_k \in \{+1, -1\}`,
but only the bound is used). Proved by unfolding `term` and `bit` and checking both
mod-$`4` branches.

This is the elementary size bound that drives every later estimate — it feeds
`abs_sum_term_le` (any $`n` consecutive terms sum to at most $`n` in absolute value) and,
through it, all of the $`O(1)`-tracking bounds of C2.
:::

:::declNotes "A362583.oddPrime_prime"
The $`k`-th odd prime $`p_k` is prime: `Nat.Prime (oddPrime k)`. Concretely `oddPrime k`
is `Nat.nth Nat.Prime (k + 1)`, the $`(k+1)`-st value of Mathlib's prime enumeration, so
`Nat.prime_nth_prime` supplies primality directly.

It is the basic fact underpinning the mod-$`4` dichotomy `oddPrime_mod_four` and licenses
the prime-specific stepping lemmas invoked along the bridge induction.
:::

:::declNotes "A362583.two_lt_oddPrime"
Every odd prime strictly exceeds $`2`: $`2 < p_k`. Since `oddPrime k` is the $`(k+1)`-st
prime and the $`0`-th prime is $`2`, strict monotonicity of `Nat.nth` on the infinite set
of primes pushes `oddPrime k` past $`2`.

This is what makes `oddPrime k` genuinely odd: combined with primality it forces
$`p_k \equiv 1` or $`3 \pmod 4` in `oddPrime_mod_four`, excluding the $`p = 2` case where
`chi` vanishes.
:::

:::declNotes "A362583.oddPrime_mod_four"
Each odd prime is congruent to $`1` or $`3` modulo $`4`:
$`p_k \equiv 1 \pmod 4 \lor p_k \equiv 3 \pmod 4`. The even residues $`0` and $`2` are
ruled out because `oddPrime k` is prime and larger than $`2`; the proof combines
`two_lt_oddPrime` with the prime "two-or-odd" dichotomy and closes by `omega`.

It certifies that the middle ($`0`-valued) branch of `chi` is never taken at an odd prime,
so `chi (oddPrime k)` collapses to a $`\pm 1` value — the content of `chi_oddPrime`.
:::

:::declNotes "A362583.chi_oddPrime"
The character value at the $`k`-th odd prime equals the bit term:
$`\chi_4(p_k) = 1 - 2 b_k`, i.e. `chi (oddPrime k) = term k`. Both cases from
`oddPrime_mod_four` are checked — $`p_k \equiv 1` gives `chi = 1` with $`b_k = 0`, and
$`p_k \equiv 3` gives `chi = -1` with $`b_k = 1`.

This is the local identity that lets the bridge replace each prime's character
contribution by its bit term, converting the race sum over primes into a partial sum over
bit indices.
:::

:::declNotes "A362583.raceSum_eq_range_sum"
`raceSum N` rewritten as an unfiltered sum over every $`p \le N`, each term being `chi p`
when $`p` is prime and $`0` otherwise:
$$`S(N) = \sum_{p \le N} \bigl(\text{if } p \text{ prime then } \chi_4(p) \text{ else } 0\bigr).`
It is `Finset.sum_filter` applied to the definition of `raceSum` as a filtered sum of `chi`
over the primes in $`[0, N]`.

The range-sum form is the one that steps cleanly under `Finset.sum_range_succ`, which is
how both `raceSum_succ_*` lemmas — and hence the bridge induction — advance $`N` to $`N+1`.
:::

:::declNotes "A362583.raceSum_succ_of_prime"
When $`n+1` is prime, extending the race sum by one step adds exactly that prime's
character value: $`S(n+1) = S(n) + \chi_4(n+1)`. Proved by unfolding both sides to range
sums and taking the `Finset.sum_range_succ` step on the `if_pos` branch.

It is one half of the inductive step of the bridge: at a genuine (odd) prime both the race
sum and the bit-index partial sum grow by the same term $`t_k`.
:::

:::declNotes "A362583.raceSum_succ_of_not_prime"
When $`n+1` is not prime, the race sum is unchanged: $`S(n+1) = S(n)`. The same range-sum
step is taken, but the `if_neg` branch contributes $`0`.

It is the complementary half of the bridge induction: a non-prime $`n+1` moves neither the
race sum nor the prime count, keeping the two sides of the bridge in lockstep.
:::

:::declNotes "A362583.primeCounting_succ_of_prime"
The prime-counting function increases by one across a prime: $`\pi(n+1) = \pi(n) + 1`. The
proof unfolds `Nat.primeCounting` to `Nat.count Nat.Prime` and applies `Nat.count_succ` on
the `if_pos` branch.

It tracks the upper index $`\pi(N) - 1` of the bit partial sum in the bridge, matching the
count's increment to the race sum's increment at each prime.
:::

:::declNotes "A362583.primeCounting_succ_of_not_prime"
The prime count is unchanged across a non-prime: $`\pi(n+1) = \pi(n)`, again via
`Nat.count_succ` but on the `if_neg` branch.

It pairs with `raceSum_succ_of_not_prime` so that non-prime steps preserve the bridge
equation on both the sum and its index simultaneously.
:::

:::declNotes "A362583.raceSum_bridge"
The bridge (C1): the race sum over primes $`\le N` equals the partial sum of bit terms over
the first $`\pi(N) - 1` odd-prime indices,
$$`S(N) = \sum_{k < \pi(N) - 1} (1 - 2 b_k).`
Natural subtraction makes the small cases uniform — $`\pi(0) = \pi(1) = 0` and $`\pi(2) = 1`
all yield the empty range, matching $`S(0) = S(1) = S(2) = 0` (because $`\chi_4(2) = 0`) —
and the inductive step uses `Nat.nth_count` to identify the newly counted prime with
$`p_{\pi(n) - 1}`.

This is the entire point of C1: it converts the number-theoretic race sum into a purely
combinatorial partial sum of the $`\pm 1` bit sequence, on which the periodic counting
argument of C2 then operates.
:::

:::declNotes "A362583.abs_sum_term_le"
Any block of $`n` consecutive terms starting at index $`a` has absolute sum at most $`n`:
$`\bigl|\sum_{k < n} t_{a+k}\bigr| \le n`. Immediate from the triangle inequality
(`Finset.abs_sum_le_sum_abs`) and `abs_term_le_one`: each of the $`n` terms is bounded by
$`1`.

It is the workhorse size bound of C2 — it caps the preperiodic prefix ($`\le N_0`), the
incomplete final window ($`< P`), and any partial block, and so it is what keeps the
deviation from linear growth bounded.
:::

:::declNotes "A362583.sum_term_window"
Under eventual periodicity of the bits with period $`P` from $`N_0` (the hypothesis
$`b_{k+P} = b_k` for all $`k \ge N_0`), a full length-$`P` window shifted forward by any
whole number $`q` of periods has the same sum as the base window:
$`\sum_{k < P} t_{N_0 + qP + k} = \sum_{k < P} t_{N_0 + k}`. Proved by induction on $`q`,
each step rewriting $`N_0 + (q+1)P + k = (N_0 + qP + k) + P` and applying periodicity to
`bit`.

It establishes that every complete period contributes the identical window sum $`W`, the
invariance that lets the running total grow at the exact constant slope $`c = W / P`.
:::

:::declNotes "A362583.sum_term_blocks"
Summing the terms over $`[0, N_0 + qP)` splits as the preperiodic prefix sum over
$`[0, N_0)` plus exactly $`q` copies of the single window sum
$`W = \sum_{k < P} t_{N_0 + k}`:
$$`\sum_{k < N_0 + qP} t_k = \Bigl(\sum_{k < N_0} t_k\Bigr) + q \cdot W.`
Proved by induction on $`q`, peeling one period with `Finset.sum_range_add` and normalizing
it to the base window via `sum_term_window`.

This is the exact accounting that $`q` complete periods contribute $`q \cdot W`, so that
against the comparison line $`c \cdot (qP) = q \cdot (cP) = q \cdot W` the periodic bulk
cancels, leaving only the two short remainders to bound.
:::

:::declNotes "A362583.abs_mul_le_of_abs_le_one"
For a real $`c` with $`|c| \le 1` and a nonnegative real $`t`, scaling cannot enlarge:
$`|c \cdot t| \le t`. Immediate from $`|c \cdot t| = |c| \cdot t \le 1 \cdot t = t`.

It is a small real-arithmetic helper used repeatedly to bound the comparison-line companion
$`c \cdot (\cdot)` of each block — prefix, remainder, and the reindexing shift — by that
block's own length.
:::

:::declNotes "A362583.abs_termSum_sub_short"
C2, short regime: when $`m \le N_0`, the partial sum $`\sum_{k < m} t_k` and its comparison
value $`c \cdot m` are each at most $`m \le N_0` in size — by `abs_sum_term_le` and
`abs_mul_le_of_abs_le_one` respectively — so their difference satisfies
$`\bigl|\sum_{k < m} t_k - c\,m\bigr| \le 2 N_0`. This dispatches the indices that never
reach the periodic tail.

It is one of the two crude regime bounds assembled by `exists_c_bound`; the constant is
deliberately generous because only a weakest-sufficient $`O(1)` bound is needed downstream.
:::

:::declNotes "A362583.abs_termSum_sub_long"
C2, long regime: for $`N_0 \le m`, write $`m = N_0 + qP + r` with $`r < P` and split
$`[0, m)` into the prefix $`[0, N_0)`, $`q` whole periods, and the partial final window
$`[N_0 + qP, m)`. Because the slope satisfies $`c \cdot P = W` (the hypothesis `hcP`), the
$`q` complete periods contribute $`c \cdot (qP)` exactly and cancel via `sum_term_blocks`;
only the prefix (size $`\le N_0`) and the partial window (size $`< P`), with their
$`c \cdot (\cdot)` companions, survive, giving
$`\bigl|\sum_{k < m} t_k - c\,m\bigr| \le 2 N_0 + 2 P`.

This is the substantive half of C2 — the estimate where eventual periodicity actually buys
linear growth with bounded error, reported by `exists_c_bound` for all $`m \ge N_0`.
:::

:::declNotes "A362583.exists_c_bound"
C2 assembled: from eventual periodicity it produces the explicit slope $`c = W / P` — the
window sum over one period divided by $`P` — proves $`|c| \le 1` because $`|W| \le P`, and
shows every partial sum tracks $`c \cdot m` within a fixed constant:
$$`\Bigl|\sum_{k < m} t_k - c\,m\Bigr| \le 2 N_0 + 2 P \qquad \text{for all } m.`
The two regimes are dispatched to the crude block bounds — $`m \le N_0` to
`abs_termSum_sub_short` and $`m \ge N_0` to `abs_termSum_sub_long`.

This is the packaged linear-with-bounded-error statement about the bit partial sums; the
top-level theorem then only has to transport it across the bridge and absorb the
$`m = \pi(N) - 1` index shift into the constant.
:::
