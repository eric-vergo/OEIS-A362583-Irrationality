/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
A362583 irrationality blueprint — declaration notes for A362583/BoundedHolo.lean.

Authored sidecar prose (`:::declNotes`) for the helper declarations of the bounded-holomorphy
toolbox that are NOT wired to a blueprint chapter node. Each block renders nothing on this page;
its prose surfaces as the informal-statement cell on the matching declaration page (preferred
over the docstring). The keys are the FULL declared names: this module mixes namespaces, so
root-namespace decls carry no prefix (`bpSeries`, `summable_bpSeries`, …) while others keep
their `Complex.`/`Real.` namespace. Wired decls (`Complex.norm_natCast_cpow_sub_add_one_cpow_le`,
`bpSeries`, `differentiableOn_bpSeries`, `norm_bpSeries_le`, `norm_bpSeries_le_const`,
`tsum_mul_cpow_neg_eq_bpSeries`) are documented on their chapter nodes and are absent here.
-/

import Verso
import VersoManual
import VersoBlueprint
import Macros
import A362583.BoundedHolo

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true

#doc (Manual) "Declaration notes: BoundedHolo" =>

:::declNotes "Complex.norm_ofReal_cpow_sub_ofReal_cpow_le"
For a complex exponent $`r` with $`\mathrm{Re}\, r \le 1` and reals $`0 < a \le b`, the complex
powers of the real casts satisfy $`\| b^{r} - a^{r} \| \le \| r \|\,(b - a)\, a^{\mathrm{Re}\, r - 1}`,
where $`a^{r}, b^{r}` are `Complex.cpow` and the right-hand $`a^{\mathrm{Re}\, r - 1}` is a real
power. The difference equals $`\int_a^b r\, t^{r - 1}\,\mathrm{d}t`, and on $`[a, b]` the integrand
has norm at most $`\| r \|\, a^{\mathrm{Re}\, r - 1}` because $`t \mapsto t^{\mathrm{Re}\, r - 1}`
is antitone once $`\mathrm{Re}\, r - 1 \le 0`. This FTC estimate is the only genuinely analytic
ingredient of the toolbox: taken at $`r = -s`, $`[a, b] = [n, n + 1]` it becomes the
Dirichlet-weight increment bound `Complex.norm_natCast_cpow_sub_add_one_cpow_le`, from which every
convergence and holomorphy result below follows. In the $`\varrho` proof it is the analytic seed
beneath Step D's holomorphy of the layer functions, which are instances of the by-parts
continuation `bpSeries`.
:::

:::declNotes "Real.natCast_rpow_neg_sub_add_one_nonneg"
For a real $`\sigma \ge 0` and a natural number $`n \ge 1`, the increment of the real power
function is nonnegative: $`0 \le n^{-\sigma} - (n + 1)^{-\sigma}` (both terms are `Real.rpow` of
$`n` and $`n + 1`). This records that $`n \mapsto n^{-\sigma}` is antitone for $`\sigma \ge 0`, so
consecutive values only decrease. Its role in the toolbox is telescoping: summed over $`n` these
nonnegative increments collapse to a single boundary term, which is how `norm_bpSeries_le` — via
the bridge `norm_cpow_neg_sub_add_one_eq` — bounds $`\| \tilde A_f(\sigma) \|` on the real axis.
For $`\varrho` that real-segment bound is what Step D uses to control the by-parts continuation on
the segment where the layers are evaluated.
:::

:::declNotes "summable_bpSeries"
Assuming bounded partial sums, $`\| \sum_{k \le n} f(k) \| \le C` for all $`n`, and
$`\mathrm{Re}\, s > 0`, the defining family of the by-parts series —
$`n \mapsto \bigl(\sum_{k \le n} f(k)\bigr)\bigl(n^{-s} - (n + 1)^{-s}\bigr)` — is `Summable`.
Convergence is absolute: by the increment bound each term's norm is $`O(n^{-\mathrm{Re}\, s - 1})`,
and $`-\mathrm{Re}\, s - 1 < -1` makes the dominating $`p`-series converge. This is the convergence
foundation of the toolbox — it is what makes `bpSeries f s` a well-defined `tsum` throughout the
open right half-plane $`\{\mathrm{Re}\, s > 0\}`, and it is upgraded verbatim to `hasSum_bpSeries`.
In the $`\varrho` proof it guarantees that the Step D layer continuations exist on
$`\{\mathrm{Re}\, s > 0\}` before their holomorphy is established.
:::

:::declNotes "hasSum_bpSeries"
Under the same hypotheses (bounded partial sums, $`\mathrm{Re}\, s > 0`), the defining family
$`n \mapsto \bigl(\sum_{k \le n} f(k)\bigr)\bigl(n^{-s} - (n + 1)^{-s}\bigr)` satisfies
`HasSum … (bpSeries f s)`: its finite partial sums converge to the value `bpSeries f s`. It is
literally `summable_bpSeries` packaged with its limit (`(summable_bpSeries hC hs).hasSum`), the
`HasSum` form being what the `Tendsto`/limit arguments consume. Its place in the toolbox is to
supply the sequential-limit step of `tsum_mul_cpow_neg_eq_bpSeries`, which identifies the raw
Dirichlet series with the continuation. For $`\varrho` that identification is a link in Step D: it
lets each layer's Dirichlet description be replaced by the holomorphic by-parts continuation.
:::

:::declNotes "differentiableOn_bpSeries_box"
With bounded partial sums and parameters $`\delta > 0`, $`R \ge 1`, this private lemma proves
`bpSeries f` holomorphic on the box $`\{ s : \delta < \mathrm{Re}\, s \} \cap B(0, R)` — a right
half-plane truncated to the open ball of radius $`R` about the origin. On such a bounded box every
term is dominated by the single, $`s`-independent summable bound $`C R\, n^{-\delta - 1}` and is
itself holomorphic, so the Weierstrass $`M`-test for series of holomorphic functions applies; a box
rather than the full half-plane is needed because no summable bound is uniform on all of
$`\{\mathrm{Re}\, s > 0\}`. It is the local ingredient that `differentiableOn_bpSeries` stitches,
box by box, into holomorphy on the whole open right half-plane. In the $`\varrho` proof that
assembled holomorphy is precisely Step D's holomorphy of the layer functions.
:::

:::declNotes "norm_cpow_neg_sub_add_one_eq"
For real $`\sigma \ge 0` and $`n \ge 1`, this private bridge lemma evaluates the complex increment
at a real argument: $`\| n^{-\sigma} - (n + 1)^{-\sigma} \| = n^{-\sigma} - (n + 1)^{-\sigma}`, with
$`\sigma` cast into $`\C` on the left and a real difference on the right. Because at a real exponent
the complex power is the cast of the real power (`Complex.ofReal_cpow`) and the real increment is
nonnegative (`Real.natCast_rpow_neg_sub_add_one_nonneg`), taking the norm simply strips the cast.
Its role is to convert the complex increment inside `bpSeries f σ` into the real, telescoping
increment used by `norm_bpSeries_le`. For $`\varrho` it is the step that turns the continuation's
norm on the real segment into a telescoping sum, yielding the uniform bound Step D relies on.
:::

:::declNotes "norm_le_two_mul_of_partialSum_le"
If every partial sum satisfies $`\| \sum_{k \le n} f(k) \| \le C`, then each coefficient is bounded
by $`\| f(n) \| \le 2 C`. Consecutive partial sums differ by $`f(n)`, so $`f(n)` is a difference of
two quantities each of norm $`\le C` (the $`n = 0` case reads the bound off the one-term partial sum
directly). This private coefficient bound is what makes the raw Dirichlet series
$`\sum_n f(n)\, n^{-s}` converge absolutely for $`\mathrm{Re}\, s > 1` (domination by
$`2 C\, n^{-\mathrm{Re}\, s}`), a hypothesis of `tsum_mul_cpow_neg_eq_bpSeries`. In the $`\varrho`
proof it belongs to the identification of the layers' Dirichlet series with their by-parts
continuation feeding Step D.
:::

:::declNotes "sum_range_mul_cpow_eq"
This private lemma is finite Abel summation for the weighted partial sum: for every $`N`,
$`\sum_{i \le N} f(i)\, i^{-s} = \bigl(\sum_{i \le N} f(i)\bigr) N^{-s} + \sum_{i < N} \bigl(\sum_{k \le i} f(k)\bigr)\bigl(i^{-s} - (i + 1)^{-s}\bigr)` —
a pure identity requiring no hypothesis on $`f`. It is a thin rearrangement of Mathlib's
`Finset.sum_range_by_parts`, splitting the Dirichlet partial sum into a boundary term plus the
by-parts partial sum. Letting $`N \to \infty` inside `tsum_mul_cpow_neg_eq_bpSeries` — where the
boundary term vanishes — is what identifies the Dirichlet series with `bpSeries`. For $`\varrho`
this algebraic backbone is what lets Step D trade the layers' Dirichlet series for the holomorphic
continuation.
:::
