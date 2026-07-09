/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
A362583 irrationality blueprint — Main Theorem chapter.

The pure-logic assembly A → B → C → D, the axiom audit, and licensing.
-/

import Verso
import VersoManual
import VersoBlueprint
import Macros
import Bibliography
import A362583.Main

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true

#doc (Manual) "Main Theorem" =>

:::group "main"
The main theorem: the prime race constant is irrational.
:::

:::theorem "thm:irrational" (lean := "A362583.irrational_ϱ") (parent := "main") (uses := "def:rho, thm:eventually-periodic, thm:race-linear, thm:race-not-linear")
*Theorem.* The prime race constant $`\varrho = \sum_{k \ge 0} b_k\,2^{-(k+1)}` — the number
whose binary expansion is $`0.b_0 b_1 b_2 \ldots_2`, where $`b_k = 1` exactly when the
$`k`-th odd prime is $`\equiv 3 \pmod 4` — is irrational.
:::

:::proof "thm:irrational"
Pure logic; no new mathematics. If $`\varrho` were rational, its bit sequence would be
eventually periodic; eventual periodicity would force the race sum onto a linear trajectory
$`|S(N) - c\,\pi(N)| \le C`; and the main analytic theorem says no such trajectory exists.
$`\blacksquare`
:::

What has been proved, precisely: the irrationality of $`\varrho` above — a statement mentioning
only the $`n`-th-prime function, remainder arithmetic, finite sums, and one convergent
series. Its analytic core, the non-linearity of the mod-4 prime race (the main analytic
theorem of the *Nonlinearity of the Prime Race* chapter), is proved in full and quantifies
over the same elementary objects. The formalization is complete and sorry-free; the axiom
audit of both reports exactly the three standard Lean axioms — propext, Classical.choice,
Quot.sound — and nothing else: no custom axioms, no unproved hypotheses, every statement
kernel-checked against Mathlib (pinned at toolchain v4.31.0).

The analytic footprint stayed as small as promised in the Introduction: the continued
$`L(s, \chi_4)` and its entirety, $`L(1, \chi_4) \ne 0`, the exponential Euler product, the
divergence of $`\sum_p 1/p` (used exactly twice, both inside the divergence transfer), and
the identity theorem. Three features of the Lean proof: the by-parts series
*defined* as the continuation, the per-prime split instead of a double-sum rearrangement, and
single-point contradictions in both cases.

The Lean sources and this blueprint are released under the Apache License 2.0.
