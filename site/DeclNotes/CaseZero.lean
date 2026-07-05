/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
import Verso
import VersoManual
import VersoBlueprint
import Macros
import Bibliography
import A362583.CaseZero

/-!
# Declaration notes: `CaseZero`

Authored sidecar prose (`:::declNotes`) for the helper declarations in
`A362583/CaseZero.lean` that carry no blueprint chapter node of their own. The
three wired declarations — `contLog`, `exp_contLog_eqOn`, and
`raceSum_not_linear` — already appear as nodes in the *Endgame* chapter and are
skipped here; the blocks below cover the four remaining, unwired helpers.

Each `:::declNotes` block renders nothing where it sits: its prose is stashed by
full declaration name and surfaces on the matching declaration page as that
declaration's informal-statement cell. This page is therefore intentionally
near-empty.
-/

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true

#doc (Manual) "Declaration notes: CaseZero" =>

:::declNotes "A362583.sum_range_fChi_vanish"
*Vanishing below the threshold.* For every natural number $`n < 2` — the two cases
$`n = 0` and $`n = 1` — the partial sum $`\sum_{k=0}^{n} f_\chi(k)` equals $`0`; both
reduce to $`f_\chi(0) = f_\chi(1) = 0`, since the length-one sum is $`f_\chi(0)` and the
length-two sum is $`f_\chi(0) + f_\chi(1)`.

This is the side condition, with threshold $`n_0 = 2`, consumed by the real-segment
by-parts bound on $`\tilde A_{f_\chi}`: that bound needs the coefficient partial sums to be
zero for all indices below $`n_0` before it can conclude $`\|\tilde A_{f_\chi}(\sigma)\| \le C`,
and this lemma supplies exactly that vanishing at the point of use inside the main analytic
theorem.
:::

:::declNotes "A362583.norm_sum_range_fChi_le"
*From bounded race to bounded coefficients.* Given a real constant $`C` with $`|S(N)| \le C`
for all $`N`, the norm of every partial sum satisfies $`\bigl\|\sum_{k=0}^{n} f_\chi(k)\bigr\|
\le C`. It is immediate from the identity that each such partial sum is precisely the integer
race sum $`S(n)`, cast into the complex numbers, so its norm is $`|S(n)| \le C`.

This lemma turns the bounded-race hypothesis $`|S(N)| \le C` into the coefficient bound
$`\|\sum_{k=0}^{n} f_\chi(k)\| \le C` on which the entire $`c = 0` endgame runs — the input both
to the holomorphy of $`\tilde A_{f_\chi}` and to the real-segment norm bound. It is applied once,
at the top of the main analytic theorem, to produce that coefficient bound.
:::

:::declNotes "A362583.differentiableOn_contLog"
*Holomorphy of $`G` on $`\Omega`.* Under the coefficient bound — all partial sums of $`f_\chi`
bounded by $`C` in norm — the continued logarithm $`G = \tilde A_{f_\chi} + B + T` is holomorphic
on the half-plane $`\Omega = \{\mathrm{Re}\, s > 1/2\}`. The by-parts series $`\tilde A_{f_\chi}`
is holomorphic on the larger $`\{\mathrm{Re}\, s > 0\}` (a consequence of the coefficient bound),
restricted here to $`\Omega`, while the explicit layers $`B` and $`T` are holomorphic on
$`\Omega` unconditionally, so their sum is too.

Holomorphy on $`\Omega` is one of the two hypotheses the identity theorem needs — the other
being agreement on $`\{\mathrm{Re}\, s > 1\}` — to propagate $`e^{G} = L(\cdot, \chi)` across the
whole half-plane. It is the step that converts the bounded-race hypothesis into holomorphy below
the line $`\mathrm{Re}\, s = 1`.
:::

:::declNotes "A362583.exp_contLog_eq"
*The half-plane identity, pointwise.* For every $`s` with $`\mathrm{Re}\, s > 1` (and under the
coefficient bound), $`\exp\bigl(G(s)\bigr) = L(s, \chi)`. On this half-plane the by-parts series
coincides with the explicit $`k = 1` layer, $`\tilde A_{f_\chi}(s) = A(s)` (the Dirichlet
identification), so $`G(s) = A(s) + B(s) + T(s)`, and the Euler-product wiring turns $`\exp` of
that sum of layers into $`L(s, \chi)`.

This is the pointwise seed for the identity theorem: it establishes $`e^{G} = L` on the open set
$`\{\mathrm{Re}\, s > 1\}`, where the Dirichlet series converge absolutely. Combined with the
holomorphy of $`G` on $`\Omega`, the identity theorem then extends it from this set — which
contains a neighborhood of $`s = 2` — to all of $`\Omega`.
:::
