/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
A362583 irrationality blueprint — Forcing C chapter.

Case c ≠ 0: a linear race |S − c·π| ≤ C forces c = 0, via the Abel bound, real-exp inversion
of the Euler identity on (1, 2], and the divergence of Σ p^(−σ) at a single point.
-/

import Verso
import VersoManual
import VersoBlueprint
import Macros
import Bibliography
import A362583.CaseNonzero

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true

#doc (Manual) "Forcing the Slope to Zero" =>

:::group "cnonzero"
The case c ≠ 0: a linear race with nonzero slope is impossible, so any linear race is a
bounded race.
:::

The analytic core refutes $`|S(N) - c\,\pi(N)| \le C` in two cases. This chapter handles
$`c \ne 0`, working entirely on the real segment $`(1, 2]` where every series converges
absolutely and no analytic continuation is needed; the conclusion is that the slope must be
zero, reducing the $`c = 0` case to the bounded-race hypothesis $`|S(N)| \le C`.

:::theorem "thm:c-zero" (lean := "A362583.c_eq_zero_of_raceSum_linear") (parent := "cnonzero") (uses := "def:raceSum, def:fChi, lem:fChi-partial-sums, lem:layerA-dirichlet, thm:bpSeries-dirichlet, lem:bpSeries-bound-const, thm:exp-L, lem:prime-sum-divergence")
*Forcing $`c = 0`.* If
$`|S(N) - c\,\pi(N)| \le C` for all $`N`, then $`c = 0`.
:::

:::proof "thm:c-zero"
Work with real $`\sigma \in (1, 2]` and write $`P(\sigma) = \sum_p p^{-\sigma}`.

*Step 1 (Abel bound).* Apply the by-parts machinery to the shifted coefficients
$`f_c(n) := f_\chi(n) - c \cdot \mathbf{1}_{\mathrm{prime}}(n)`: their partial sums are
exactly the race deviation $`S(n) - c\,\pi(n)`, bounded by $`C` by hypothesis and vanishing
below $`n = 2`. The real-segment bound plus the Dirichlet-series identification give
$$`\bigl| A(\sigma) - c\, P(\sigma) \bigr| \;\le\; C \qquad \text{on } (1, 2].`

*Step 2 (logarithm bound).* For real $`\sigma > 1` the three layers are real, so the Euler
identity reads $`L(\sigma, \chi) = e^{A(\sigma) + B(\sigma) + T(\sigma)}` — a *positive
real* — and injectivity of the real exponential inverts it to
$`\ln L(\sigma) = A(\sigma) + B(\sigma) + T(\sigma)`; no complex logarithm is ever inverted.
At the endpoint, $`L(1, \chi) > 0`: it is the limit of the positive values
$`L(\sigma)` as $`\sigma \downarrow 1` (the one plain one-sided limit surviving in the whole
development), and it is nonzero by Mathlib's nonvanishing at $`1`. Hence
$`\mathrm{Re}\, L(\cdot, \chi)` is continuous and positive on the compact $`[1, 2]`, its
logarithm is bounded there by some $`K_0`, and with the layer bounds
$`0 \le B \le c_B`, $`|T| \le c_T` this yields
$`|A(\sigma)| \le K := K_0 + c_B + c_T` on $`(1, 2]`.

*Step 3 (single-point contradiction).* If $`c \ne 0`, steps 1–2 force
$`P(\sigma) \le (C + K)/|c|` throughout $`(1, 2]`. But the prime-sum divergence supplies a
single $`\sigma^* \in (1, 2)` with $`P(\sigma^*) > (C + K)/|c|`. Contradiction; hence
$`c = 0`. $`\blacksquare`
:::
