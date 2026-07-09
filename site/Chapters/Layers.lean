/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
A362583 irrationality blueprint — Layers chapter.

The mod-4 character and the layer decomposition of −log(1 − χ(p)p^(−s)): the k = 2 layer B
and its real companion, the k ≥ 3 per-prime tail and layer T, the log series, the two
divergence-transfer lemmas, and the per-prime split.
-/

import Verso
import VersoManual
import VersoBlueprint
import Macros
import Bibliography
import A362583.Layers

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true

#doc (Manual) "Layers" =>

:::group "layers"
The mod-4 character, the k = 2 and k ≥ 3 layers of the Euler-product logarithm, the
power series of the logarithm, and the divergence transfer.
:::

The analytic core expands $`-\log(1 - \chi(p) p^{-s})` as a power series in $`\chi(p) p^{-s}`
and groups the terms by the exponent $`k`: the $`k = 1` layer carries the race, the $`k = 2`
layer $`B` diverges as $`s \downarrow 1/2`, and the $`k \ge 3` tail $`T` is uniformly
bounded. This chapter builds $`B` and $`T` with their bounds, the divergence-transfer and
logarithm-series lemmas they share, and the per-prime split that feeds the Euler product in
the next chapter.

:::definition "def:raceKernel" (lean := "A362583.raceKernel") (parent := "layers")
*The race kernel.* The elementary integer function $`\kappa(n) = +1` if $`n \equiv 1 \pmod 4`,
$`-1` if $`n \equiv 3 \pmod 4`, and $`0` otherwise — definitionally the integrand of the race
sum, so $`S(N) = \sum_{p \le N} \kappa(p)`.
:::

:::definition "def:chi" (lean := "A362583.χ") (parent := "layers") (uses := "def:raceKernel")
*The mod-4 character.* $`\chi` is Mathlib's $`\chi_4` pushed into $`\C` as a Dirichlet
character mod $`4`; it is nonprincipal ($`\chi \ne 1`, witnessed at $`3`). The bridge
$`\chi(n) = \kappa(n)` for every natural $`n` keeps the elementary statements — phrased with
the race kernel $`\kappa` — aligned with the character world the analysis lives in.
:::

:::definition "def:layerB" (lean := "A362583.layerB") (parent := "layers")
*The $`k = 2` layer* $`B`. Since $`\chi(p)^2 = 1` for odd $`p` and $`\chi(2)^2 = 0`,
$$`B(s) \;=\; \tfrac12 \sum_{p \text{ odd}} p^{-2s},`
realized in Lean with an if-mask at $`p = 2`. It is holomorphic on
$`\Omega = \{\mathrm{Re}\, s > 1/2\}` by locally uniform convergence of its partial sums.
:::

:::definition "def:layerBReal" (lean := "A362583.layerBReal") (parent := "layers") (uses := "def:layerB")
*Real companion of the $`k = 2` layer.* On the real axis $`B` is repackaged with real powers
as $`B(\sigma)`, agreeing with the complex $`B` at real arguments. This is the form the
$`c = 0` case evaluates: $`B(\sigma) \ge 0`, and $`B(\sigma) \le c_B := \tfrac12 \sum_p p^{-2}`
for $`\sigma \ge 1`. The blow-up of $`B(\sigma)` as $`\sigma \downarrow 1/2` is *not* proved
here — it is one instance of the divergence transfer below.
:::

:::definition "def:tp" (lean := "A362583.tp") (parent := "layers") (uses := "def:chi")
*The per-prime $`k \ge 3` tail.* With $`z_p := \chi(p)\, p^{-s}`,
$$`t_p(s) \;=\; \sum_{k \ge 0} \frac{z_p^{\,k+3}}{k+3}`
— the terms of the logarithm series from the third onward. Geometric tails give the
per-prime bound $`|t_p(s)| \le \tfrac43 p^{-3/2}` on $`\mathrm{Re}\, s \ge 1/2`. (The constant
is deliberately loose; nothing downstream needs a tight bound.)
:::

:::definition "def:layerT" (lean := "A362583.layerT") (parent := "layers") (uses := "def:tp")
*The $`k \ge 3` layer* $`T(s) = \sum_p t_p(s)`, summed over all primes. The per-prime bound
$`|t_p| \le \tfrac43 p^{-3/2}` feeds the Weierstrass $`M`-test, so $`T` is holomorphic on
$`\Omega` with the *uniform* bound $`\|T(s)\| \le c_T := \tfrac43 \sum_p p^{-3/2}` on
$`\mathrm{Re}\, s \ge 1/2`, and real on the real axis.
:::

:::lemma_ "lem:log-series" (lean := "A362583.hasSum_neg_log_one_sub") (parent := "layers")
*Logarithm series.* For $`\|z\| < 1`,
$$`\sum_{k \ge 1} \frac{z^k}{k} \;=\; -\operatorname{Log}(1 - z)`
with the principal complex logarithm, in summed (HasSum) form. All uses have
$`\|z_p\| \le 2^{-\sigma} < 1/2` since only $`\sigma > 1` is ever consumed.
:::

:::proof "lem:log-series"
This is Mathlib's Taylor expansion of $`-\operatorname{Log}(1 - z)`, quoted verbatim (the
$`k = 0` term is $`z^0/0 = 0` by Lean's convention, so the sum may be read from $`k \ge 1`).
The branch of the logarithm — the one genuine analytic subtlety — is pinned inside Mathlib's
own proof, so no separate branch-pinning argument is needed here. $`\blacksquare`
:::

:::lemma_ "lem:prime-sum-divergence" (lean := "A362583.exists_one_lt_tsum_primes_rpow_gt") (parent := "layers")
*Prime-sum divergence.* For every $`M` and $`\eta > 0` there is $`\sigma \in (1, 1+\eta)` with
$`P(\sigma) := \sum_p p^{-\sigma} > M`.
:::

:::proof "lem:prime-sum-divergence"
Because $`\sum_p 1/p` diverges — the *sole* quantitative prime input of the whole development —
its finite subsums are unbounded, so choose a *finite* set $`F` of primes with
$`\sum_{p \in F} 1/p > M`. At $`\sigma = 1` the finite sum $`\sum_{p \in F} p^{-\sigma}` equals
$`\sum_{p \in F} 1/p > M`; being continuous in $`\sigma`, it still exceeds $`M` at some
$`\sigma \in (1, 1+\eta)`. There $`\sigma > 1`, so the full series $`P(\sigma) = \sum_p p^{-\sigma}`
converges, and its nonnegative terms make it at least the finite subsum:
$`P(\sigma) \ge \sum_{p \in F} p^{-\sigma} > M`. A single point $`\sigma^*` suffices — no
filters or limits appear. $`\blacksquare`
:::

:::lemma_ "lem:divergence-transfer" (lean := "A362583.exists_layerBReal_gt") (parent := "layers") (uses := "def:layerBReal")
*Divergence transfer to layer $`B`.* For every $`M` and $`\eta > 0` there is
$`\sigma \in (1/2, 1/2+\eta)` with $`B(\sigma) > M` — the blow-up of the $`k = 2` layer just
above $`1/2` that drives the $`c = 0` case.
:::

:::proof "lem:divergence-transfer"
Recall $`B(\sigma) = \tfrac12 \sum_{p \text{ odd}} p^{-2\sigma}`. The divergence of $`\sum_p 1/p`
survives dropping the $`p = 2` term, so the finite subsums over odd primes are unbounded:
choose a *finite* set $`F` of odd primes with $`\sum_{p \in F} 1/p > 2M`. At $`\sigma = 1/2`,
$`\sum_{p \in F} p^{-2\sigma} = \sum_{p \in F} p^{-1} > 2M`, and by continuity in $`\sigma` this
persists at some $`\sigma \in (1/2, 1/2+\eta)`. There the odd-prime series dominates its finite
subsum over $`F` (nonnegative terms), so
$`B(\sigma) \ge \tfrac12 \sum_{p \in F} p^{-2\sigma} > \tfrac12 \cdot 2M = M`. As in the
prime-sum instance, a single point $`\sigma^*` suffices. $`\blacksquare`
:::

:::lemma_ "lem:neg-log-split" (lean := "A362583.neg_log_split") (parent := "layers") (uses := "lem:log-series, def:chi, def:layerB, def:tp")
*Per-prime split.* For $`\mathrm{Re}\, s > 1` and each prime $`p`, with
$`z_p = \chi(p) p^{-s}` (so $`\|z_p\| \le 2^{-\sigma} < 1/2`),
$$`-\operatorname{Log}\bigl(1 - z_p\bigr) \;=\; \chi(p)\, p^{-s} \;+\; \tfrac12\, \chi(p)^2\, p^{-2s} \;+\; t_p(s).`
:::

:::proof "lem:neg-log-split"
Since $`\|z_p\| \le 2^{-\sigma} < 1`, the logarithm series applies:
$`-\operatorname{Log}(1 - z_p) = \sum_{k \ge 1} z_p^{\,k}/k`. Peel off the first three terms.
The $`k = 0` term is $`0`; $`k = 1` gives $`z_p = \chi(p)\, p^{-s}`; $`k = 2` gives
$`z_p^2/2 = \tfrac12\, \chi(p)^2\, p^{-2s}`; and the remaining tail
$`\sum_{k \ge 0} z_p^{\,k+3}/(k+3)` is *definitionally* $`t_p(s)` — that is the reason for the
exact shape of the definition of $`t_p`. Splitting finitely many terms off one convergent
series is not a rearrangement, and summing this identity over $`p` (next chapter) uses only
linearity of three convergent series, so the double-sum rearrangement of the original informal
argument is avoided entirely. $`\blacksquare`
:::
