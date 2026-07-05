/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
import Verso
import VersoManual
import VersoBlueprint
import Macros
import A362583.DigitLayer

/-!
# Declaration notes: DigitLayer

Authored sidecar prose (`:::declNotes`) for the helper declarations of
`A362583/DigitLayer.lean` that are **not** wired to a blueprint chapter node.
Each block renders nothing here; the prose surfaces as the informal-statement
cell on the matching declaration page (in preference to the docstring). The
notes cover the Step A bit/prime bookkeeping and the Step B binary-tail lemmas
B1–B5.
-/

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true

#doc (Manual) "Declaration notes: DigitLayer" =>

:::declNotes "A362583.bit_eq_one_iff"
$`b_k = 1` if and only if the $`k`-th odd prime satisfies $`p_k \equiv 3 \pmod 4`; this is
just the definitional unfolding of $`b_k`. It is the bookkeeping bridge that lets Step A turn
"infinitely many primes $`\equiv 3 \pmod 4`" (Dirichlet) into "infinitely many indices with
$`b_k = 1`".
:::

:::declNotes "A362583.bit_eq_zero_iff"
$`b_k = 0` if and only if $`p_k \not\equiv 3 \pmod 4`; since every odd prime is $`1` or $`3`
mod $`4`, this is the same as $`p_k \equiv 1 \pmod 4`. The Lean statement is written literally
with the negated congruence. It is the companion of the previous lemma, feeding the
infinitely-many-zeros half of Step A.
:::

:::declNotes "A362583.oddPrime_count"
For a prime $`p \ne 2`, write $`c` for the number of primes strictly below $`p`; then $`p` is
the odd prime of index $`c - 1`, i.e. $`p_{c-1} = p`. Equivalently, the map
$`p \mapsto (\#\{\text{primes} < p\}) - 1` inverts the odd-prime enumeration on odd primes. This
pointwise inverse is what makes the prime-to-index transfer of Step A well-defined.
:::

:::declNotes "A362583.infinite_oddPrime_index"
If $`S` is an infinite set of primes with $`2 \notin S`, then the index set
$`\{k \mid p_k \in S\}` is infinite. The proof injects $`S` into the indices via
$`p \mapsto (\#\{\text{primes} < p\}) - 1`, with the previous lemma as its one-sided inverse.
This is the transfer engine of Step A: it carries Dirichlet's infinitude of a residue class over
to infinitude of bit indices.
:::

:::declNotes "A362583.infinite_primes_three_mod_four"
There are infinitely many primes $`p` with $`p \equiv 3 \pmod 4`. This is Dirichlet's theorem on
primes in arithmetic progressions at modulus $`4`, converted here from Mathlib's
$`\mathbb{Z}/4\mathbb{Z}`-valued form to plain remainder arithmetic. Together with the transfer
lemma it delivers the infinitely-many-ones half of Step A.
:::

:::declNotes "A362583.infinite_primes_one_mod_four"
There are infinitely many primes $`p` with $`p \equiv 1 \pmod 4` — Dirichlet's theorem at
modulus $`4` for the residue class $`1`, again rewritten from the $`\mathbb{Z}/4\mathbb{Z}` form
into remainder arithmetic. It feeds the transfer lemma to produce infinitely many indices with
$`b_k = 0`, the second half of Step A.
:::

:::declNotes "A362583.t"
The binary tail $`t_k := \sum_{j \ge 0} b_{k+j}\, 2^{-(j+1)}`, the real number whose binary
digits are $`b_k, b_{k+1}, \ldots`; in particular $`t_0 = \varrho`. This is the central object
of Step B: rationality of $`\varrho` forces the tails to repeat, which forces the digit sequence
to be eventually periodic.
:::

:::declNotes "A362583.t_def"
The definitional equation $`t_k = \sum_{j \ge 0} b_{k+j}\, 2^{-(j+1)}`, holding by
reflexivity. It exists only to expose $`t_k` as its defining infinite sum, so that later Step B
lemmas can rewrite and manipulate the series directly.
:::

:::declNotes "A362583.bit_le_one"
Every bit satisfies $`b_k \le 1` (as a natural number). A one-line bookkeeping bound that
underlies the term-by-term comparison of the tail with the geometric series.
:::

:::declNotes "A362583.bit_zero_or_one"
Every bit is either $`0` or $`1`. This exhaustiveness is used repeatedly across Step B — for
instance when reading a bit off its tail, and when propagating a tail collision to bit equality.
:::

:::declNotes "A362583.term_nonneg"
Each summand $`b_{k+j}/2^{\,j+1}` of the tail $`t_k` is nonnegative. It supplies the
nonnegativity hypothesis for the comparison test and for the strict-positivity argument (B1).
:::

:::declNotes "A362583.term_le_geom"
Each summand $`b_{k+j}/2^{\,j+1}` of the tail is bounded above by $`(1/2)^{\,j+1}`, the matching
term of the geometric series. This domination is what makes the tail summable and bounds it above
by $`1`.
:::

:::declNotes "A362583.summable_geom"
The comparison series $`\sum_{j \ge 0} (1/2)^{\,j+1}` is summable. It is the majorant for every
tail, and the source of both the summability of $`t_k` and its strict upper bound.
:::

:::declNotes "A362583.tsum_geom"
The comparison series sums to $`\sum_{j \ge 0} (1/2)^{\,j+1} = 1`. This exact value is what pins
the strict upper bound $`t_k < 1` in B1.
:::

:::declNotes "A362583.summable_t"
For every $`k`, the defining series of $`t_k` is summable, by comparison
($`0 \le \text{term} \le (1/2)^{\,j+1}`) with the geometric series. Summability is what makes
$`t_k` well-defined and licenses splitting off its first term to derive the recurrence (B2).
:::

:::declNotes "A362583.t_pos"
*(B1)* $`0 < t_k` for every $`k`. Because Step A guarantees infinitely many later ones, some
strictly positive term appears in the tail and forces it above $`0`. This is the lower half of
B1, $`t_k \in (0,1)`.
:::

:::declNotes "A362583.t_lt_one"
*(B1)* $`t_k < 1` for every $`k`. Infinitely many later zeros (Step A) make the tail strictly
dominated by the geometric series, whose sum is $`1`. This is the upper half of B1; together with
positivity it places every tail strictly inside $`(0,1)`.
:::

:::declNotes "A362583.t_rec"
*(B2)* The digit recurrence $`t_k = (b_k + t_{k+1})/2`, obtained by peeling the $`j = 0` term off
the tail. This is the algebraic heart of Step B, from which the tail's determination of the bit
follows.
:::

:::declNotes "A362583.t_succ"
*(B2)* The rearranged recurrence $`t_{k+1} = 2\,t_k - b_k`. It expresses the next tail from the
current one and is the form used in the fractional-part induction (B3) and in propagating a tail
collision (B5).
:::

:::declNotes "A362583.bit_one_iff_half_lt"
*(B2)* $`b_k = 1` if and only if $`t_k > 1/2`. Combined with B1 at $`k+1`, the recurrence forces
$`t_k \in (1/2,1)` when $`b_k = 1` and $`t_k \in (0,1/2)` when $`b_k = 0`; in particular
$`t_k \ne 1/2`, so the tail *determines* the bit. This determination is the key mechanism of
Step B.
:::

:::declNotes "A362583.bit_eq_of_t_eq"
*(B2 consequence)* Equal tails have equal bits: $`t_m = t_n` implies $`b_m = b_n`. It is the
immediate corollary of the bit-from-tail characterization, and the engine that turns a single
tail collision into matching bits.
:::

:::declNotes "A362583.t_eq_add"
*(B5)* If $`t_m = t_n`, then $`t_{m+i} = t_{n+i}` for all $`i \ge 0`. The induction on $`i` uses
B2's determinism — equal tails give equal bits, and hence, by $`t_{k+1} = 2t_k - b_k`, equal next
tails. This is B5: a tail collision propagates to every later offset.
:::

:::declNotes "A362583.t_eq_fract"
*(B3)* $`t_k = \operatorname{fract}(2^k \varrho)`, the fractional part of $`2^k \varrho`. Since
$`2^k\varrho` differs from $`t_k` by an integer (its binary prefix) and $`t_k \in (0,1)` by B1,
the fractional part is exactly $`t_k`. This identity is the bridge from digit combinatorics to
arithmetic.
:::

:::declNotes "A362583.exists_t_collision"
*(B4)* If $`\varrho` is not irrational — hence rational, with some denominator $`b` — then two
distinct tails coincide: there exist $`m < n` with $`t_m = t_n`. Via B3 each
$`t_k = \operatorname{fract}(2^k \varrho)` lies in the finite set
$`\{0, 1/b, \ldots, (b-1)/b\}`, so the pigeonhole principle forces a repeat. This collision is
the seed that B5 grows into eventual periodicity.
:::
