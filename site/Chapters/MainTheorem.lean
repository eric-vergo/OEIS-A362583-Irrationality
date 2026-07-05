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
The main theorem: the A362583 constant is irrational.
:::

:::theorem "thm:irrational" (lean := "A362583.irrational_x") (parent := "main") (uses := "def:x, thm:eventually-periodic, thm:race-linear, thm:race-not-linear")
*Theorem.* The constant $`x = 0.b_0 b_1 b_2 \ldots` in binary — where $`b_k = 1` exactly
when the $`k`-th odd prime is $`\equiv 3 \pmod 4` — is irrational.
:::

:::proof "thm:irrational"
Pure logic; no new mathematics. If $`x` were rational, Step B (which consumes Step A) would
make its bit sequence eventually periodic; Step C would then put the race sum on a linear
trajectory $`|S(N) - c\,\pi(N)| \le C`; and Step D says no such trajectory exists.
$`\blacksquare`
:::

What has been proved, precisely: two theorems whose statements mention only the
$`n`-th-prime function, remainder arithmetic, finite sums, and one convergent series — the
irrationality of $`x` above, and the non-linearity of the mod-4 prime race (the main
analytic theorem of the Endgame chapter). The formalization is complete and sorry-free; the
axiom audit of both headline theorems reports exactly the three standard Lean axioms —
propext, Classical.choice, Quot.sound — and nothing else: no custom axioms, no
unproved hypotheses, every statement kernel-checked against Mathlib (pinned at toolchain
v4.31.0).

The analytic footprint stayed as small as promised in the Introduction: the continued
$`L(s, \chi_4)` and its entirety, $`L(1, \chi_4) \ne 0`, the exponential Euler product, the
divergence of $`\sum_p 1/p` (used exactly twice, both inside the divergence transfer), and
the identity theorem. Three design choices shaped the Lean proof: the by-parts series
*defined* as the continuation, the per-prime split instead of a double-sum rearrangement, and
single-point contradictions in both endgames.

The Lean sources and this blueprint are dedicated to the public domain under CC0 1.0
Universal.
