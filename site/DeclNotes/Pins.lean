/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-!
# Declaration notes: Pins

Authored sidecar prose (`:::declNotes`) for the sanity-pin helpers of
`A362583/Pins.lean`: the `private` lemmas fixing the small values of `oddPrime`
and `bit`, together with the `nth`/`count` helper behind them. None of these
lemmas is wired to a blueprint chapter node, so the prose here surfaces only on
their declaration pages — each block renders nothing where it is written.

The bracketing `1/2 < ϱ < 1` and `raceSum 10 = -1` pins in that module are
anonymous `example`s, not named declarations, so they cannot carry notes; they
are described in prose in the Definitions chapter instead.
-/

import Verso
import VersoManual
import VersoBlueprint
import Macros

open Verso.Genre
open Verso.Genre.Manual
open Informal

set_option doc.verso true

#doc (Manual) "Declaration notes: Pins" =>

:::declNotes "A362583.oddPrime_eq_of_count"
The reusable pin helper behind every `oddPrime` value below: to certify $`p_k = m`
it suffices that $`m` is prime and that $`m` is the $`(k+1)`-th prime by count —
`Nat.count Nat.Prime m = k + 1` — both of which `decide` settles for small $`m`.
It turns each concrete pin into a finite computation through Mathlib's
`Nat.nth`/`Nat.count` Galois connection, so the indexing convention the value pins
rely on is itself checked.
:::

:::declNotes "A362583.oddPrime_zero"
The first odd prime is $`3` — $`p_0 = 3`; pins the indexing convention so the digit
examples stay honest.
:::

:::declNotes "A362583.oddPrime_one"
The second odd prime is $`5` — $`p_1 = 5`; pins the indexing convention so the digit
examples stay honest.
:::

:::declNotes "A362583.oddPrime_two"
The third odd prime is $`7` — $`p_2 = 7`; pins the indexing convention so the digit
examples stay honest.
:::

:::declNotes "A362583.oddPrime_three"
The fourth odd prime is $`11` — $`p_3 = 11`; pins the indexing convention so the
digit examples stay honest.
:::

:::declNotes "A362583.oddPrime_four"
The fifth odd prime is $`13` — $`p_4 = 13`; pins the indexing convention so the digit
examples stay honest.
:::

:::declNotes "A362583.oddPrime_five"
The sixth odd prime is $`17` — $`p_5 = 17`; pins the indexing convention so the digit
examples stay honest.
:::

:::declNotes "A362583.oddPrime_six"
The seventh odd prime is $`19` — $`p_6 = 19`; pins the indexing convention so the
digit examples stay honest.
:::

:::declNotes "A362583.oddPrime_seven"
The eighth odd prime is $`23` — $`p_7 = 23`; pins the indexing convention so the digit
examples stay honest.
:::

:::declNotes "A362583.bit_zero"
$`b_0 = 1`, because $`p_0 = 3 \equiv 3 \pmod 4`; pins the mod-4 classification so the
binary digits of $`\varrho` stay honest.
:::

:::declNotes "A362583.bit_one"
$`b_1 = 0`, because $`p_1 = 5 \equiv 1 \pmod 4`; pins the mod-4 classification so the
binary digits of $`\varrho` stay honest.
:::

:::declNotes "A362583.bit_two"
$`b_2 = 1`, because $`p_2 = 7 \equiv 3 \pmod 4`; pins the mod-4 classification so the
binary digits of $`\varrho` stay honest.
:::

:::declNotes "A362583.bit_three"
$`b_3 = 1`, because $`p_3 = 11 \equiv 3 \pmod 4`; pins the mod-4 classification so the
binary digits of $`\varrho` stay honest.
:::

:::declNotes "A362583.bit_four"
$`b_4 = 0`, because $`p_4 = 13 \equiv 1 \pmod 4`; pins the mod-4 classification so the
binary digits of $`\varrho` stay honest.
:::

:::declNotes "A362583.bit_five"
$`b_5 = 0`, because $`p_5 = 17 \equiv 1 \pmod 4`; pins the mod-4 classification so the
binary digits of $`\varrho` stay honest.
:::

:::declNotes "A362583.bit_six"
$`b_6 = 1`, because $`p_6 = 19 \equiv 3 \pmod 4`; pins the mod-4 classification so the
binary digits of $`\varrho` stay honest.
:::

:::declNotes "A362583.bit_seven"
$`b_7 = 1`, because $`p_7 = 23 \equiv 3 \pmod 4`; pins the mod-4 classification so the
binary digits of $`\varrho` stay honest.
:::
