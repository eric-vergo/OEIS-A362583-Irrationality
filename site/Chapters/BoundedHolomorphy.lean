/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
A362583 irrationality blueprint — Bounded Holomorphy chapter.

A standalone, project-independent toolbox: Dirichlet series with bounded partial sums continue
holomorphically to {Re s > 0} via the by-parts series. Root-namespace, Mathlib-style; upstream
candidate.
-/

import Verso
import VersoManual
import VersoBlueprint
import Macros
import Bibliography
import A362583.BoundedHolo

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true

#doc (Manual) "Bounded Holomorphy" =>

:::group "n1"
Dirichlet series with bounded partial sums: the by-parts series is the analytic continuation
to the right half-plane.
:::

This chapter is deliberately project-independent. It is stated for an arbitrary coefficient
sequence $`f : \mathbb{N} \to \C` and developed in Mathlib style in the root namespace (not
the project namespace), and it is a candidate for upstreaming — including the increment bound
below, which Mathlib currently lacks. Rather than continuing the Dirichlet series after the
fact, the continuation *is defined* as a series, so the only analysis is one application of
the fundamental theorem of calculus.

:::lemma_ "lem:increment" (lean := "Complex.norm_natCast_cpow_sub_add_one_cpow_le") (parent := "n1")
*Increment bound.* For $`s \in \C` with $`-1 \le \mathrm{Re}\, s` and a
natural number $`n \ge 1`,
$$`\bigl\| n^{-s} - (n+1)^{-s} \bigr\| \;\le\; \|s\|\; n^{-\mathrm{Re}\,s - 1}.`
:::

:::proof "lem:increment"
The bound is the special case $`r = -s`, $`[a, b] = [n, n+1]` (so $`b - a = 1`) of the general
estimate
$$`\bigl\| b^{r} - a^{r} \bigr\| \;\le\; \|r\|\,(b - a)\, a^{\mathrm{Re}\,r - 1} \qquad (0 < a \le b,\ \ \mathrm{Re}\,r \le 1);`
here $`\mathrm{Re}(-s) = -\mathrm{Re}\, s \le 1` because $`-1 \le \mathrm{Re}\, s`.

The estimate is the only genuinely analytic ingredient of the chapter, and it is a single
application of the fundamental theorem of calculus. Since $`t \mapsto t^{r}` has derivative
$`r\, t^{r-1}`,
$$`b^{r} - a^{r} \;=\; \int_a^b r\, t^{r-1}\, \mathrm{d}t.`
On $`[a, b]` the integrand has norm
$`\|r\|\, t^{\mathrm{Re}\,r - 1} \le \|r\|\, a^{\mathrm{Re}\,r - 1}`,
because $`t \mapsto t^{\mathrm{Re}\,r - 1}` is antitone when $`\mathrm{Re}\,r - 1 \le 0`;
bounding the integral of this constant majorant over an interval of length $`b - a` gives the
estimate. Everything downstream is then index bookkeeping, telescoping, and a Weierstrass
$`M`-test. $`\blacksquare`
:::

:::definition "def:bpSeries" (lean := "bpSeries") (parent := "n1")
The *by-parts series* of $`f : \mathbb{N} \to \C` is
$$`\tilde A_f(s) \;=\; \sum_{n \ge 0} \Bigl(\sum_{k \le n} f(k)\Bigr)\bigl(n^{-s} - (n+1)^{-s}\bigr).`
It is what discrete Abel summation produces from the Dirichlet series
$`\sum_n f(n)\, n^{-s}`, but here it is taken as the *definition* of the continuation object.
No hypothesis on $`f(0)` is needed anywhere: Lean's junk value $`0^{-s} = 0` (for
$`s \ne 0`) makes the $`n = 0` term harmless, and the identification below is exact as
stated.
:::

:::lemma_ "lem:box-summable" (lean := "summable_bpSeries_boxBound") (parent := "n1") (uses := "def:bpSeries")
*Summable majorant.* For $`C, R \ge 0` and $`\delta > 0` the sequence
$$`n \longmapsto \begin{cases} C & n = 0, \\ C\,R\, n^{-\delta - 1} & n \ge 1 \end{cases}`
is summable — the Weierstrass majorant for the by-parts terms on a box
$`\{\mathrm{Re}\, s > \delta\} \cap B(0, R)`.
:::

:::proof "lem:box-summable"
Adjusting the single $`n = 0` term does not affect summability, and
$`\sum_{n \ge 1} n^{-\delta - 1}` converges because $`\delta + 1 > 1`. $`\blacksquare`
:::

:::lemma_ "lem:term-holo" (lean := "differentiableOn_bpSeries_term") (parent := "n1") (uses := "def:bpSeries")
*Term holomorphy.* For $`\delta > 0` and every $`n`, the by-parts term
$`s \mapsto \bigl(\sum_{k \le n} f(k)\bigr)\bigl(n^{-s} - (n+1)^{-s}\bigr)` is holomorphic on the
box $`\{\mathrm{Re}\, s > \delta\} \cap B(0, R)`.
:::

:::proof "lem:term-holo"
A finite constant multiple of a difference of the entire maps $`s \mapsto n^{-s}` and
$`s \mapsto (n+1)^{-s}`. $`\blacksquare`
:::

:::lemma_ "lem:term-box-bound" (lean := "norm_bpSeries_term_le_boxBound") (parent := "n1") (uses := "def:bpSeries, lem:increment")
*Uniform term bound.* If the partial sums of $`f` are bounded by $`C`, then on the box
$`\{\mathrm{Re}\, s > \delta\} \cap B(0, R)` (with $`R \ge 0`, $`\delta > 0`) the $`n`-th
by-parts term has norm at most the majorant of the previous lemma: $`C` for $`n = 0` and
$`C\,R\, n^{-\delta - 1}` for $`n \ge 1`.
:::

:::proof "lem:term-box-bound"
Bound the coefficient by $`C` and the increment $`\|n^{-s} - (n+1)^{-s}\|` by the increment
bound $`\|s\|\, n^{-\mathrm{Re}\,s - 1}`, then use $`\|s\| < R` and
$`n^{-\mathrm{Re}\,s - 1} \le n^{-\delta - 1}` on the box. $`\blacksquare`
:::

:::theorem "thm:bpSeries-holo-box" (lean := "differentiableOn_bpSeries_box") (parent := "n1") (uses := "lem:box-summable, lem:term-holo, lem:term-box-bound")
*Holomorphy on a box.* If the partial sums of $`f` are bounded by $`C`, then for $`\delta > 0`
and $`R \ge 1` the by-parts series $`\tilde A_f` is holomorphic on the box
$`\{\mathrm{Re}\, s > \delta\} \cap B(0, R)`.
:::

:::proof "thm:bpSeries-holo-box"
Each term is holomorphic on the box, and their norms are dominated there by a single summable
majorant, so the Weierstrass $`M`-test for series of holomorphic functions (the
locally-uniform-limits theorem) applies. $`\blacksquare`
:::

:::theorem "thm:bpSeries-holo" (lean := "differentiableOn_bpSeries") (parent := "n1") (uses := "def:bpSeries, thm:bpSeries-holo-box")
*Holomorphy.* If the partial sums satisfy
$`\bigl\| \sum_{k \le n} f(k) \bigr\| \le C` for all $`n`, then $`\tilde A_f` is holomorphic
on the open right half-plane $`\{\mathrm{Re}\, s > 0\}`.
:::

:::proof "thm:bpSeries-holo"
Holomorphy is local. Around any $`s_0` with $`\mathrm{Re}\, s_0 > 0`, choose
$`0 < \delta < \mathrm{Re}\, s_0` and $`R \ge 1` with $`\|s_0\| < R`; the previous theorem makes
$`\tilde A_f` holomorphic on the box $`\{\mathrm{Re}\, s > \delta\} \cap B(0, R)`, hence at
$`s_0`. As $`s_0` was arbitrary, $`\tilde A_f` is holomorphic on all of
$`\{\mathrm{Re}\, s > 0\}`. Consumers needing a smaller half-plane, such as
$`\Omega = \{\mathrm{Re}\, s > 1/2\}` downstream, simply restrict. $`\blacksquare`
:::

:::lemma_ "lem:term-real-bound" (lean := "norm_bpSeries_term_le") (parent := "n1") (uses := "def:bpSeries")
*Real-axis term bound.* If the partial sums of $`f` are bounded by $`C`, then for real
$`\sigma \ge 0` and $`n \ge 1` the $`n`-th by-parts term satisfies
$$`\Bigl\| \Bigl(\sum_{k \le n} f(k)\Bigr)\bigl(n^{-\sigma} - (n+1)^{-\sigma}\bigr) \Bigr\|
   \;\le\; C\,\bigl(n^{-\sigma} - (n+1)^{-\sigma}\bigr).`
:::

:::proof "lem:term-real-bound"
On the real axis $`n \mapsto n^{-\sigma}` is antitone, so the increment
$`n^{-\sigma} - (n+1)^{-\sigma}` is a nonnegative real of exactly that norm; multiply by the
coefficient bound $`C`. $`\blacksquare`
:::

:::lemma_ "lem:partial-majorant" (lean := "sum_range_norm_bpSeries_le") (parent := "n1") (uses := "lem:term-real-bound")
*Telescoping partial sums.* Under the bounded-partial-sum hypothesis, if the partial sums of
$`f` vanish for $`n < n_0` (with $`n_0 \ge 1`), then for real $`\sigma \ge 0` and every $`N`
$$`\sum_{n < N} \Bigl\| \Bigl(\sum_{k \le n} f(k)\Bigr)\bigl(n^{-\sigma} - (n+1)^{-\sigma}\bigr) \Bigr\|
   \;\le\; C\, n_0^{-\sigma}.`
:::

:::proof "lem:partial-majorant"
The terms below $`n_0` vanish; for $`n \ge n_0` apply the real-axis term bound and telescope,
$`\sum_{n < N} C\,(n^{-\sigma} - (n+1)^{-\sigma}) = C\,(n_0^{-\sigma} - N^{-\sigma}) \le C\, n_0^{-\sigma}`.
$`\blacksquare`
:::

:::lemma_ "lem:bpSeries-bound" (lean := "norm_bpSeries_le") (parent := "n1") (uses := "def:bpSeries, lem:partial-majorant")
*Real-segment bound.* Suppose the partial sums of $`f` are bounded by $`C` and vanish
for $`n < n_0` (with $`n_0 \ge 1`). Then for real $`\sigma \ge 0`,
$$`\bigl\| \tilde A_f(\sigma) \bigr\| \;\le\; C\, n_0^{-\sigma}.`
:::

:::proof "lem:bpSeries-bound"
The partial sums of $`\sum_n \|\text{term}\|` are bounded by $`C\, n_0^{-\sigma}` (previous
lemma), so the full series $`\|\tilde A_f(\sigma)\| \le \sum_n \|\text{term}\|` inherits that
bound. In the race application the coefficients are supported on primes, so the partial sums
below $`n = 2` vanish, giving $`n_0 = 2` and the bound $`C \cdot 2^{-\sigma}`. $`\blacksquare`
:::

:::lemma_ "lem:bpSeries-bound-const" (lean := "norm_bpSeries_le_const") (parent := "n1") (uses := "lem:bpSeries-bound")
*Real-segment bound, constant form.* Under the same hypotheses, for real $`\sigma \ge 0`,
$$`\bigl\| \tilde A_f(\sigma) \bigr\| \;\le\; C.`
This is the convenience form consumed downstream, where only a uniform bound on the segment is
needed.
:::

:::proof "lem:bpSeries-bound-const"
Immediate from the real-segment bound: $`n_0^{-\sigma} \le 1` because $`n_0 \ge 1` and
$`-\sigma \le 0`, so $`C\, n_0^{-\sigma} \le C`. $`\blacksquare`
:::

:::lemma_ "lem:boundary-term" (lean := "tendsto_boundary_term") (parent := "n1") (uses := "def:bpSeries")
*Vanishing boundary term.* If the partial sums of $`f` are bounded by $`C`, then for
$`\mathrm{Re}\, s > 0` the Abel boundary term tends to zero:
$$`\Bigl(\sum_{i \le N} f(i)\Bigr) N^{-s} \;\longrightarrow\; 0 \qquad (N \to \infty).`
:::

:::proof "lem:boundary-term"
Its norm is at most $`C\, N^{-\mathrm{Re}\, s}`, which tends to $`0` because
$`\mathrm{Re}\, s > 0`. $`\blacksquare`
:::

:::theorem "thm:bpSeries-dirichlet" (lean := "tsum_mul_cpow_neg_eq_bpSeries") (parent := "n1") (uses := "def:bpSeries, lem:boundary-term")
*Identification with the Dirichlet series.* If the partial sums of $`f` are bounded
by $`C`, then for $`\mathrm{Re}\, s > 1`
$$`\sum_{n \ge 0} f(n)\, n^{-s} \;=\; \tilde A_f(s).`
Together with the holomorphy theorem this says: *the by-parts series is the analytic
continuation of the Dirichlet series* from $`\{\mathrm{Re}\, s > 1\}` to
$`\{\mathrm{Re}\, s > 0\}` — obtained here by definition rather than by continuation, so no
measurability, integrability, or dominated-convergence side conditions ever arise.
:::

:::proof "thm:bpSeries-dirichlet"
Bounded partial sums bound the coefficients, $`\|f(n)\| \le 2C` (consecutive partial sums
differ by $`f(n)`), so the Dirichlet series $`\sum_n f(n)\, n^{-s}` converges absolutely for
$`\mathrm{Re}\, s > 1` (domination by $`2C\, n^{-\mathrm{Re}\,s}`). Finite Abel summation
(summation by parts) gives, for every $`N`,
$$`\sum_{i \le N} f(i)\, i^{-s} \;=\; \Bigl(\sum_{i \le N} f(i)\Bigr) N^{-s}
   \;+\; \sum_{i < N} \Bigl(\sum_{k \le i} f(k)\Bigr)\bigl(i^{-s} - (i+1)^{-s}\bigr).`
Let $`N \to \infty`. The left side tends to $`\sum_n f(n)\, n^{-s}`; the boundary term tends to
$`0`, since
$`\bigl\|\bigl(\sum_{k \le N} f(k)\bigr) N^{-s}\bigr\| \le C\, N^{-\mathrm{Re}\,s} \to 0`;
and the by-parts partial sum tends to $`\tilde A_f(s)`. Uniqueness of limits yields the
identity. No hypothesis on $`f(0)` is needed: the $`n = 0` Dirichlet term vanishes because
$`0^{-s} = 0` for $`s \ne 0`. $`\blacksquare`
:::
