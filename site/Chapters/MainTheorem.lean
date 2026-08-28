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
The main theorem: Rokicki's constant is irrational.
:::

:::theorem "thm:irrational" (lean := "A362583.irrational_ϱ") (parent := "main") (uses := "def:rho, thm:eventually-periodic, thm:race-linear, thm:race-not-linear")
*Theorem.* Rokicki's constant $`\varrho = \sum_{k \ge 0} b_k\,2^{-(k+1)}` — the number
whose binary expansion is $`0.b_0 b_1 b_2 \ldots_2`, where $`b_k = 1`  when the
$`k`-th odd prime is $`\equiv 3 \pmod 4` — is irrational.
:::

:::proof "thm:irrational"
 If $`\varrho` were rational, its bit sequence would be
eventually periodic; eventual periodicity would force the race sum onto a linear trajectory
$`|S(N) - c\,\pi(N)| \le C`; and the main analytic theorem says no such trajectory exists.
$`\blacksquare`
:::


The Lean sources and this blueprint are released under the Apache License 2.0.
