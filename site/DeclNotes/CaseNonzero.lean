/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
A362583 irrationality blueprint — declaration notes for A362583/CaseNonzero.lean.

Authored sidecar prose for every helper declaration in the c ≠ 0 branch of Step D that is
not wired to a blueprint chapter node. Each :::declNotes block renders nothing where it is
written; its prose surfaces on the corresponding declaration page as the informal-statement
cell (in preference to the docstring). The one wired result of that module,
A362583.c_eq_zero_of_raceSum_linear, is the theorem of the "Forcing the Slope to Zero"
chapter and is deliberately omitted here.
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

#doc (Manual) "Declaration notes: CaseNonzero" =>

%%%
number := false
%%%

:::declNotes "A362583.fSub"
The *shifted coefficient* is the complex number $`f_c(n) = f_\chi(n) - c\,\mathbf{1}_{\mathrm{prime}}(n)`: the race-kernel coefficient $`f_\chi(n)` minus $`c` times the prime indicator $`\mathbf{1}_{\mathrm{prime}}(n)` (which is $`1` when $`n` is prime and $`0` otherwise). Its partial sums recover the race deviation $`S(n) - c\,\pi(n)`, and viewed as Dirichlet coefficients they generate $`A(s) - c\,P(s)`. All of Step 1 is organized around this single family.
:::

:::declNotes "A362583.primeCounting_eq_card_filter"
Mathlib's prime-counting function satisfies $`\pi(n) = \#\{\,k \le n : k \text{ prime}\,\}`, the cardinality of the primes in $`\mathrm{range}(n+1)`. This rewrites Nat.primeCounting — defined through a running count — into the finite-set-cardinality shape that $`S(N)` uses, confirming that the two expressions count exactly the same primes $`\le N`.
:::

:::declNotes "A362583.sum_range_ite_prime"
Summing the complex prime indicator over $`k \le n` counts the primes up to $`n`: $`\sum_{k \le n} \mathbf{1}_{\mathrm{prime}}(k) = \pi(n)`, cast into $`\mathbb{C}`. This computes the prime-indicator half of the $`f_c` partial sums, feeding the closed form for $`\sum_{k \le n} f_c(k)`.
:::

:::declNotes "A362583.sum_range_fSub"
The partial sum $`\sum_{k \le n} f_c(k)` equals the real number $`S(n) - c\,\pi(n)`, cast into $`\mathbb{C}`. This is the heart of the Abel setup: it identifies the coefficient partial sums with precisely the race deviation that the linearity hypothesis controls.
:::

:::declNotes "A362583.norm_sum_range_fSub_le"
Under the linearity hypothesis $`|S(N) - c\,\pi(N)| \le C` for all $`N`, the partial sums of $`f_c` satisfy $`\bigl\|\sum_{k \le n} f_c(k)\bigr\| \le C`. This packages the hypothesis into the uniform partial-sum bound that the by-parts summation machinery requires.
:::

:::declNotes "A362583.sum_range_fSub_eq_zero"
For $`n < 2` the partial sum $`\sum_{k \le n} f_c(k)` vanishes, since there are no primes below $`2` and $`f_\chi(0) = f_\chi(1) = 0`. This supplies the "low partial sums are zero" side condition (with cutoff $`n_0 = 2`) that Abel summation needs.
:::

:::declNotes "A362583.norm_fChi_le_one"
The race-kernel coefficient is bounded in norm by $`1`, i.e. $`\|f_\chi(n)\| \le 1`, because $`f_\chi(n)` takes values in $`\{-1, 0, 1\}`. This is the pointwise estimate that dominates the $`f_\chi` Dirichlet series by $`\sum_n n^{-\sigma}`, giving absolute convergence.
:::

:::declNotes "A362583.summable_fChi_mul_cpow"
For $`\mathrm{Re}\,s > 1` the Dirichlet series $`\sum_n f_\chi(n)\,n^{-s}` is summable (absolutely convergent), by comparison with $`\sum_n n^{-\mathrm{Re}\,s}`. This is one of the two summability facts that let the combined series of $`f_c` be split linearly into its $`A` and $`P` pieces.
:::

:::declNotes "A362583.summable_ite_prime_mul_cpow"
For $`\mathrm{Re}\,s > 1` the prime-indicator Dirichlet series $`\sum_n \mathbf{1}_{\mathrm{prime}}(n)\,n^{-s}` is summable, again by comparison with $`\sum_n n^{-\mathrm{Re}\,s}`. It is the second summability fact needed to split the series of $`f_c` into its two summable halves.
:::

:::declNotes "A362583.tsum_primes_cpow_eq_tsum_ite"
The sum over the prime subtype equals the indicator sum over all naturals: $`\sum_p p^{-s} = \sum_n \mathbf{1}_{\mathrm{prime}}(n)\,n^{-s}`, unconditionally. This subtype-to-indicator bridge lets the prime series $`P(s)` be written as a genuine $`\mathbb{N}`-indexed Dirichlet series, matching the shape of the $`f_c` split so the two can be subtracted term by term.
:::

:::declNotes "A362583.bpSeries_fSub_eq"
Given the uniform partial-sum bound on $`f_c` and $`\mathrm{Re}\,s > 1`, the by-parts series of $`f_c` equals $`A(s) - c\,P(s)`, where $`P(s) = \sum_p p^{-s}` is the complex prime series. This identifies the abstract Abel/by-parts series with the analytic difference of the layer function $`A` and the prime series, transferring the coefficient bound onto $`A - c\,P`.
:::

:::declNotes "A362583.primeSum"
The *real prime series* $`P(\sigma) = \sum_p p^{-\sigma}`, the sum of $`p^{-\sigma}` over the primes at a real exponent $`\sigma`. Step 3 shows that this quantity would have to stay bounded on $`(1, 2]` if $`c \ne 0` — which its divergence as $`\sigma \downarrow 1` forbids.
:::

:::declNotes "A362583.primeSum_ofReal"
At a real argument the complex prime series is the cast of the real one: $`\sum_p p^{-\sigma} = P(\sigma)` in $`\mathbb{C}`. This real-to-complex bridge turns the complex identity for the by-parts series into a statement about the real $`P(\sigma)`, which is what the real-form Abel bound needs.
:::

:::declNotes "A362583.abs_layerAReal_sub_mul_primeSum_le"
*Step 1, in real form.* Under the linearity hypothesis, $`|A(\sigma) - c\,P(\sigma)| \le C` for every real $`\sigma > 1`. This is the Abel bound the endgame consumes: it couples the layer $`A` and the prime series $`P` through the constant $`C`, supplying one of the two inequalities that drive the final contradiction.
:::

:::declNotes "A362583.LFunction_ofReal_eq_exp"
For real $`\sigma > 1`, the L-function value is the cast of a positive real exponential: $`L(\sigma, \chi) = \exp\!\bigl(A(\sigma) + B(\sigma) + T(\sigma)\bigr)`. This real-exponential form of the Euler identity is the pivot of Step 2 — because the right-hand side is a genuine positive real, a *real* logarithm (never a complex one) recovers $`A(\sigma)`.
:::

:::declNotes "A362583.LFunction_ofReal_re_pos"
For real $`\sigma > 1`, the real part of the L-function is positive: $`\mathrm{Re}\,L(\sigma, \chi) > 0`, immediately from the exponential form. Positivity on the open segment is what lets the logarithm be taken and, at the boundary, seeds the one-sided limit of positive values.
:::

:::declNotes "A362583.LFunction_ofReal_im_eq_zero"
For real $`\sigma > 1`, the L-function is real: $`\mathrm{Im}\,L(\sigma, \chi) = 0`, since it is the cast of a real number. This vanishing feeds the one-sided-limit argument that pins $`\mathrm{Im}\,L(1, \chi) = 0` at the endpoint.
:::

:::declNotes "A362583.continuous_LFunction_ofReal_re"
The map $`\sigma \mapsto \mathrm{Re}\,L(\sigma, \chi)` is continuous on all of $`\mathbb{R}`, obtained from differentiability of $`L` (valid because $`\chi \ne 1`) composed with the real embedding and the real-part projection. Continuity underlies both the compact-interval maximum on $`[1, 2]` and the limit taken at $`\sigma = 1`.
:::

:::declNotes "A362583.continuous_LFunction_ofReal_im"
The map $`\sigma \mapsto \mathrm{Im}\,L(\sigma, \chi)` is continuous on $`\mathbb{R}`, by the same differentiability-of-$`L` argument. This continuity of the imaginary part is what makes the one-sided limit at $`\sigma = 1` legitimate.
:::

:::declNotes "A362583.LFunction_one_re_pos"
At the endpoint $`\sigma = 1`, the real part is positive: $`\mathrm{Re}\,L(1, \chi) > 0`. The proof combines three facts — $`\mathrm{Im}\,L(1, \chi) = 0` as a limit of the vanishing imaginary parts from the right, $`\mathrm{Re}\,L(1, \chi) \ge 0` as a limit of positive real parts, and $`L(1, \chi) \ne 0` from Mathlib's nonvanishing of $`L` at $`1` — so a nonnegative real part that cannot be zero is strictly positive. This closes positivity at the boundary, so $`\mathrm{Re}\,L` is positive across the whole compact $`[1, 2]`.
:::

:::declNotes "A362583.LFunction_ofReal_re_pos_of_mem_Icc"
For every $`\sigma` in the closed interval $`[1, 2]`, $`\mathrm{Re}\,L(\sigma, \chi) > 0`: the points $`\sigma > 1` come from the open-segment positivity, and the left endpoint $`\sigma = 1` from the boundary lemma. Positivity on the whole compact is what makes $`\log \mathrm{Re}\,L` defined and continuous there, enabling a uniform bound.
:::

:::declNotes "A362583.layerAReal_eq_log_sub"
For real $`\sigma > 1`, inverting the exponential form gives $`A(\sigma) = \log\bigl(\mathrm{Re}\,L(\sigma, \chi)\bigr) - B(\sigma) - T(\sigma)`, using the real logarithm (so no branch cut arises). Writing $`A` this way means that a bound on $`\log \mathrm{Re}\,L`, together with the layer bounds on $`B` and $`T`, directly bounds $`A`.
:::

:::declNotes "A362583.exists_bound_abs_layerAReal"
*Step 2.* There is a constant $`K` with $`|A(\sigma)| \le K` for all $`\sigma \in (1, 2]`. It is assembled as $`K = K_0 + C_B + C_T`, where $`K_0` bounds $`|\log \mathrm{Re}\,L|` on the compact $`[1, 2]` (from continuity plus positivity), $`C_B` bounds $`B` (which is also nonnegative), and $`C_T` bounds $`|T|`. Together with the Abel bound of Step 1, this uniform control of $`A` is exactly what forces $`P(\sigma)` to stay bounded once $`c \ne 0`.
:::
