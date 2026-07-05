/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
A362583 irrationality blueprint — Endgame chapter.

The continued logarithm, the identity theorem on {Re s > 1/2}, and the single-point blow-up
just above 1/2 — the main analytic theorem raceSum_not_linear.
-/

import Verso
import VersoManual
import VersoBlueprint
import Macros
import Bibliography
import A362583.CaseZero

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true

#doc (Manual) "Endgame" =>

:::group "czero"
Case c = 0 of Step D: a bounded race would continue log L(s, χ₄) past Re s = 1/2 minus
an explicitly divergent term — which the finite value L(1/2, χ₄) forbids.
:::

With the slope forced to zero, assume $`|S(N)| \le C` for all $`N`. This is the classical
"prime-square term" mechanism behind oscillation results for real characters, specialized to
the weakest usable statement: the $`k = 2` layer $`B` diverges at $`1/2^{+}` while everything
else stays bounded, so the identity $`e^{G} = L` cannot survive down to $`1/2`.

:::definition "def:contLog" (lean := "A362583.contLog") (parent := "czero") (uses := "def:bpSeries, def:fChi, def:layerB, def:layerT")
*The continued logarithm.* $`G := \tilde A_{f_\chi} + B + T`, the sum of the by-parts
continuation of the $`k = 1` layer and the two explicit layers. The definition itself is
unconditional; under the bounded-race hypothesis, $`\tilde A_{f_\chi}` is holomorphic on
$`\{\mathrm{Re}\, s > 0\}` (its coefficient partial sums are exactly the race sums, bounded
by $`C`), and $`B`, $`T` are holomorphic on $`\Omega = \{\mathrm{Re}\, s > 1/2\}`
unconditionally — so $`G` is holomorphic on $`\Omega`, the largest half-plane the argument
needs.
:::

:::theorem "thm:eqOn" (lean := "A362583.exp_contLog_eqOn") (parent := "czero") (uses := "def:contLog, thm:exp-L, thm:bpSeries-dirichlet")
*Identity theorem.* Under the bounded-race hypothesis,
$$`\exp\bigl(G(s)\bigr) \;=\; L(s, \chi) \qquad \text{for all } s \in \Omega = \{\mathrm{Re}\, s > 1/2\}.`
:::

:::proof "thm:eqOn"
On $`\{\mathrm{Re}\, s > 1\}` the by-parts series agrees with $`A` (Dirichlet identification),
so $`e^{G} = e^{A+B+T} = L` there by the Euler wiring. Both sides are holomorphic on $`\Omega`
— $`G` under the bounded-race hypothesis, and $`L` because it is entire — and $`\Omega` is open
and convex, hence preconnected. They agree on the open set $`\{\mathrm{Re}\, s > 1\}`, which
contains a neighborhood of $`s = 2`, so Mathlib's identity theorem for holomorphic functions
propagates the identity to all of $`\Omega`. This is the only place the bounded-race hypothesis
converts into information *below* $`\mathrm{Re}\, s = 1`. $`\blacksquare`
:::

:::theorem "thm:race-not-linear" (lean := "A362583.raceSum_not_linear") (parent := "czero") (uses := "def:raceSum, thm:c-zero, thm:eqOn, thm:bpSeries-holo, lem:divergence-transfer")
*Main analytic theorem* (Step D). There are no constants $`c, C` with
$$`\bigl| S(N) - c\,\pi(N) \bigr| \;\le\; C \qquad \text{for all } N.`
The mod-4 prime race is never linear in the prime count. This statement is meaningful
independently of the prime race constant $`\varrho`, and like the irrationality theorem it quantifies only
over elementary objects — it is the analytic core that the headline result rests on, an
internal milestone rather than a separately advertised deliverable.
:::

:::proof "thm:race-not-linear"
Suppose such $`c, C` exist. The forcing theorem gives $`c = 0`, so $`|S(N)| \le C`; the
partial sums of $`f_\chi` are then bounded by $`C`, and the identity theorem applies.

*(Single-point form.)* $`L(\cdot, \chi)` is entire, hence continuous at $`1/2`: there
are $`M_0 := \|L(1/2, \chi)\| + 1` and $`\delta_0 > 0` with $`\|L(s, \chi)\| < M_0`
whenever $`\|s - 1/2\| < \delta_0`. The divergence transfer supplies a
*single* real point $`\sigma^* \in (1/2,\, 1/2 + \delta_0)` with
$$`B(\sigma^*) \;>\; \ln M_0 + C + C_T.`
At $`s = \sigma^*` all three pieces of $`G` are real, with
$`\mathrm{Re}\, \tilde A_{f_\chi}(\sigma^*) \ge -C` (real-segment bound, $`n_0 = 2`) and
$`T(\sigma^*) \ge -C_T` (uniform bound), so
$$`\|L(\sigma^*, \chi)\| \;=\; e^{\mathrm{Re}\, G(\sigma^*)} \;\ge\; e^{\,B(\sigma^*) - C - C_T} \;>\; M_0,`
contradicting the continuity bound at the very same point. No limit toward $`1/2^{+}` is
taken — the contradiction is evaluated at the one point $`\sigma^*`.
$`\blacksquare`
:::
