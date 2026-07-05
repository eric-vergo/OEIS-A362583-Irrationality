/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
A362583 irrationality blueprint — declaration notes for `A362583/EulerLog.lean`.

Authored sidecar prose (`:::declNotes`) for the helper declarations of the Euler-log
module that are NOT wired to a blueprint chapter node: the layer-`A` summability fact,
the two `fChi` boundary lemmas, the real companion `layerAReal`, and the real-axis
agreement / real-part / imaginary-part lemmas. Each block renders nothing inline; the
prose surfaces on the corresponding declaration page as its informal-statement cell.
-/

import Verso
import VersoManual
import VersoBlueprint
import Macros
import Bibliography
import A362583.EulerLog

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true

#doc (Manual) "Declaration notes: EulerLog" =>

:::declNotes "A362583.summable_layerA_term"
*Summability of the layer-$`A` integrand.* For $`s` with $`\mathrm{Re}\, s > 1`, the
prime-indexed family $`p \mapsto \chi(p)\, p^{-s}` (indexed over the subtype of primes) is
summable; it is deduced from norm-summability of the same term by discarding the norm. This
is the convergence fact that makes $`A(s) = \sum_p \chi(p)\, p^{-s}` a well-defined sum, and
it is the hypothesis that licenses splitting the prime sum by linearity in the layer-split
theorem — the $`k = 1` piece's share of the absolute convergence that keeps the Euler-log
rearrangement honest.
:::

:::declNotes "A362583.fChi_zero"
*Vanishing at $`0`.* The coefficient sequence satisfies $`f_\chi(0) = 0`, since $`0` is not
prime and $`f_\chi` returns $`0` at every non-prime index. This pins the bottom of the range:
summing $`f_\chi` from index $`0` picks up nothing before the first prime $`2`, so the partial
sums stay exactly the race sums $`\sum_{k \le n} f_\chi(k) = S(n)` and the summation-by-parts
continuation of layer $`A` indexes cleanly from $`0`.
:::

:::declNotes "A362583.fChi_one"
*Vanishing at $`1`.* Likewise $`f_\chi(1) = 0`, because $`1` is not prime. It is the companion
boundary fact to $`f_\chi(0) = 0`: the two smallest indices contribute nothing, matching that
the smallest prime is $`2`, which keeps the low-order bookkeeping of the by-parts machinery
free of edge cases.
:::

:::declNotes "A362583.layerAReal"
*Real companion of layer $`A`.* For a real argument $`\sigma`, define $`A_{\mathbb{R}}(\sigma)
= \sum_p \kappa(p)\, p^{-\sigma}`, the real-valued series over the primes that uses the real
power $`p^{-\sigma}` and the integer race kernel $`\kappa(p)` (cast to $`\mathbb{R}`) in place
of the character $`\chi(p)`. This is the honestly real object shadowing the complex $`A` along
the real axis; the Step D endgame reasons about it directly, and the three lemmas that follow
tie the complex $`A(\sigma)` back to it.
:::

:::declNotes "A362583.layerA_ofReal"
*Agreement on the real axis.* For every real $`\sigma`, the complex layer at the real point
$`\sigma` equals the complex cast of its real companion $`A_{\mathbb{R}}(\sigma) = \sum_p
\kappa(p)\, p^{-\sigma}`; that is, $`A(\sigma) = A_{\mathbb{R}}(\sigma)` in $`\C`. The proof
pushes the real-to-complex coercion through the sum and matches it termwise via the bridge
$`\chi(p) = \kappa(p)` on prime natural casts, and is unconditional — no summability
hypothesis is needed. This identity is the single bridge from which the real-part and
imaginary-part statements below are read off.
:::

:::declNotes "A362583.layerA_im"
*Real on the real axis.* At any real point $`\sigma`, the imaginary part of the complex layer
vanishes, $`\mathrm{Im}\, A(\sigma) = 0`. This follows immediately from the agreement lemma,
since a real number cast into $`\C` has zero imaginary part. It certifies that $`A(\sigma)` is
genuinely real for real $`\sigma`, a fact the Step D endgame depends on when it manipulates
$`A` along the real line.
:::

:::declNotes "A362583.layerA_re"
*Real part on the real axis.* At a real point $`\sigma`, the real part of the complex layer is
exactly its real companion, $`\mathrm{Re}\, A(\sigma) = A_{\mathbb{R}}(\sigma)`, the real
series $`\sum_p \kappa(p)\, p^{-\sigma}`. Again this is read off the agreement lemma, taking
the real part of a real cast. It lets the analysis replace $`\mathrm{Re}\, A(\sigma)` by that
concrete real quantity, carrying the conclusions of the complex $`L`-function machinery back
to something that can be bounded.
:::
