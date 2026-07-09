/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
A362583 irrationality blueprint — Euler Product chapter.

The layer split summed over primes, the wiring to Mathlib's continued Dirichlet L-function,
and the ℕ-indexed coefficient bridge fChi whose partial sums are exactly the race sums.
-/

import Verso
import VersoManual
import VersoBlueprint
import Macros
import Bibliography
import A362583.EulerLog

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true

#doc (Manual) "The Euler Product" =>

:::group "euler"
The k = 1 layer, the split of the Euler-product logarithm into layers, the identity
exp(A + B + T) = L(s, χ), and the coefficient bridge to the race sum.
:::

Two named Mathlib facts are consumed here: the identification of the analytically continued
$`L`-function with its Dirichlet series on $`\{\mathrm{Re}\, s > 1\}`, and the exponential
form of the Euler product. Everything else is series bookkeeping.

:::definition "def:layerA" (lean := "A362583.layerA") (parent := "euler") (uses := "def:chi")
*The $`k = 1` layer.* $`A(s) = \sum_p \chi(p)\, p^{-s}`, absolutely convergent for
$`\mathrm{Re}\, s > 1`. This is the layer that carries the race: everything the analytic
argument ever learns about the distribution of the bits flows through $`A`.
:::

:::theorem "thm:tsum-split" (lean := "A362583.tsum_neg_log_eq_layers") (parent := "euler") (uses := "lem:neg-log-split, def:layerA, def:layerB, def:layerT")
*Layer split.* For $`\mathrm{Re}\, s > 1`,
$$`\sum_p -\operatorname{Log}\bigl(1 - \chi(p)\, p^{-s}\bigr) \;=\; A(s) + B(s) + T(s).`
:::

:::proof "thm:tsum-split"
Rewrite each summand by the per-prime split, turning the left side into
$`\sum_p \bigl(\chi(p)\, p^{-s} + \tfrac12\, \chi(p)^2\, p^{-2s} + t_p(s)\bigr)`. The three
resulting prime-indexed series converge absolutely — dominated by $`p^{-\sigma}`,
$`\tfrac12 p^{-2\sigma}`, and the geometric-tail bound $`\tfrac43 p^{-3/2}` respectively — so
linearity of convergent series splits the sum into $`\sum_p \chi(p)\, p^{-s}`,
$`\sum_p \tfrac12 \chi(p)^2\, p^{-2s}`, and $`\sum_p t_p(s)`. The first is $`A(s)` and the third
is $`T(s)` by definition; the middle piece is $`B(s)`, since $`\chi(2)^2 = 0` and
$`\chi(p)^2 = 1` for odd $`p`. No absolutely-summable-double-family machinery appears.
$`\blacksquare`
:::

:::theorem "thm:exp-L" (lean := "A362583.exp_layers_eq_LFunction") (parent := "euler") (uses := "thm:tsum-split")
*Euler wiring.* For $`\mathrm{Re}\, s > 1`,
$$`\exp\bigl(A(s) + B(s) + T(s)\bigr) \;=\; L(s, \chi),`
where $`L` is Mathlib's analytically continued Dirichlet $`L`-function of $`\chi` — an
*entire* function, since $`\chi` is nonprincipal. From here on, "the $`L`-function" always
means this continued object; its two properties used later are entirety (hence continuity at
$`1/2`) and nonvanishing at $`s = 1`.
:::

:::proof "thm:exp-L"
By the layer split, $`A(s) + B(s) + T(s) = \sum_p -\operatorname{Log}(1 - \chi(p)\, p^{-s})`.
Exponentiating, Mathlib's exponential form of the Euler product for a Dirichlet $`L`-series
turns $`\exp` of that prime sum into the $`L`-series $`\sum_n \chi(n)\, n^{-s}`; and on
$`\{\mathrm{Re}\, s > 1\}` the analytically continued $`L`-function agrees with its
$`L`-series. Composing the three gives $`\exp(A + B + T) = L(s, \chi)`. That $`\chi` is
nonprincipal ($`\chi \ne 1`, witnessed at $`3`) is what makes the continued $`L` entire.
$`\blacksquare`
:::

:::definition "def:fChi" (lean := "A362583.fChi") (parent := "euler") (uses := "def:raceKernel")
*The coefficient bridge.* Define $`f_\chi : \mathbb{N} \to \C` by $`f_\chi(n) = \kappa(n)` if
$`n` is prime and $`0` otherwise — the race kernel restricted to the primes, packaged as an
$`\mathbb{N}`-indexed coefficient sequence. The two exact identities developed in the lemmas
below feed $`f_\chi` to the by-parts machinery.
:::

:::lemma_ "lem:fChi-partial-sums" (lean := "A362583.sum_range_fChi") (parent := "euler") (uses := "def:fChi, def:raceSum")
*Partial sums are race sums.* $`\sum_{k \le n} f_\chi(k) = S(n)`. The partial sums of
$`f_\chi` *are* the race sums, so a bounded race is precisely the "bounded partial sums"
hypothesis the by-parts machinery needs.
:::

:::proof "lem:fChi-partial-sums"
Unfold both sides: $`f_\chi(k)` is $`\kappa(k)` when $`k` is prime and $`0` otherwise, while
$`S(n) = \sum_{p \le n} \kappa(p)` ranges over primes. Summing $`f_\chi` over $`k \le n`
discards the non-prime indices, whose terms are $`0`, leaving exactly the prime-filtered sum
that defines $`S(n)`. Unconditional bookkeeping — no summability is involved. $`\blacksquare`
:::

:::lemma_ "lem:layerA-dirichlet" (lean := "A362583.layerA_eq_tsum_fChi") (parent := "euler") (uses := "def:fChi, def:layerA")
*Layer $`A` as a Dirichlet series.* $`A(s) = \sum_{n \ge 0} f_\chi(n)\, n^{-s}`. This exhibits
$`A` as the $`\mathbb{N}`-indexed Dirichlet series of $`f_\chi`, so its by-parts series
continues $`A`.
:::

:::proof "lem:layerA-dirichlet"
The layer $`A(s) = \sum_p \chi(p)\, p^{-s}` is a sum over the subtype of primes; rewriting it
as a sum over all $`n \in \mathbb{N}` inserts the prime indicator, giving
$`\sum_n \mathbf{1}_{\text{prime}}(n)\, \chi(n)\, n^{-s}`. At a prime $`n` the indicator leaves
$`\chi(n)\, n^{-s} = f_\chi(n)\, n^{-s}` (the bridge $`\chi = \kappa` on natural casts); off the
primes both $`f_\chi(n)` and the indicator vanish. Hence $`A(s) = \sum_n f_\chi(n)\, n^{-s}`.
Unconditional — a subtype-versus-indicator rewriting; no summability is needed. $`\blacksquare`
:::
