/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
A362583 irrationality blueprint — declaration notes for the Layers module.

Authored sidecar prose (`:::declNotes`) for every helper declaration in
`A362583/Layers.lean` that is *not* wired to a blueprint chapter node. Each block
renders nothing where it is written; the declaration-page emitter surfaces it as the
informal-statement cell of the corresponding declaration page. Blocks are keyed by the
full declaration name (all live in `namespace A362583`) and ordered to follow the source.
-/

import Verso
import VersoManual
import VersoBlueprint
import Macros
import Bibliography
import A362583.Layers

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true

#doc (Manual) "Declaration notes: Layers" =>

:::declNotes "A362583.raceSum_eq_sum_raceKernel"
Rewrites the Chebyshev race sum as a sum of the named integer kernel over primes:
$`S(N) = \sum_{p \le N} \kappa(p)`, an equality that holds definitionally. It is the
bookkeeping identity that lets the elementary $`S(N)` be handled through $`\kappa`, and —
composed with the bridge $`\chi(n) = \kappa(n)` — pulled into the character world where
Step D's analysis takes place.
:::

:::declNotes "A362583.χ_ne_one"
States that the mod-4 character $`\chi` is not the principal character: $`\chi \ne 1`. The two
already disagree at the unit $`3 \in \Z/4\Z`, where $`\chi(3) = -1` while the principal
character is $`1`. Nonprincipality is the standing hypothesis the analytic core consumes — a
nonprincipal Dirichlet character has an entire $`L`-function, with no pole at $`s = 1`.
:::

:::declNotes "A362583.χ_natCast_eq_kernel"
On the residue of a natural number, the character equals the integer race kernel:
$`\chi(n) = \kappa(n)` in $`\C` for every $`n \in \N`. This is the elementary bridge tying the
analytic character to the integrand of $`S(N)`; it drives the real-axis agreements (such as
`tp_ofReal`) and the eventual identification of the layer sums back with the race.
:::

:::declNotes "A362583.χ_natCast_eq_ite"
The same character–kernel bridge written in literal if-chain form: $`\chi(n)` equals $`+1` when
$`n \equiv 1 \pmod 4`, $`-1` when $`n \equiv 3 \pmod 4`, and $`0` otherwise (cast to $`\C`). It
is the variant whose right-hand side matches the race sum's integrand syntactically, so it can
be rewritten directly against $`S(N)`.
:::

:::declNotes "A362583.χ_natCast_one_mod_four"
The residue-value lemma $`\chi(n) = 1` whenever $`n \equiv 1 \pmod 4`. One of the three
elementary evaluations of $`\chi` on natural casts, feeding the kernel bridge and the
odd-prime computation $`\chi(p)^2 = 1`.
:::

:::declNotes "A362583.χ_natCast_three_mod_four"
The residue-value lemma $`\chi(n) = -1` whenever $`n \equiv 3 \pmod 4`. Together with the
$`1 \bmod 4` and even cases it pins down $`\chi` on every natural cast, underpinning both the
kernel bridge and $`\chi(p)^2 = 1` for odd $`p`.
:::

:::declNotes "A362583.χ_natCast_even"
The residue-value lemma $`\chi(n) = 0` whenever $`n` is even. It records that $`\chi` kills the
even residues, which is exactly why the prime $`2` drops out of the $`k = 2` layer $`B`.
:::

:::declNotes "A362583.norm_χ_le_one"
The character is bounded by $`1` in modulus everywhere: $`\|\chi(a)\| \le 1` for every residue
$`a \in \Z/4\Z` (each value is a root of unity or $`0`). This crude uniform bound is the seed of
every Euler-factor norm estimate downstream.
:::

:::declNotes "A362583.χ_sq_eq_ite"
For a prime $`p`, the square of the character is $`\chi(p)^2 = 0` when $`p = 2` and $`1` when
$`p` is odd. This is what identifies the $`k = 2` layer with $`B`: the $`\chi(p)^2` factor
collapses to the if-mask at $`p = 2` that defines $`B` (see `tsum_term_two_eq_layerB`).
:::

:::declNotes "A362583.norm_χ_mul_cpow_le"
The base norm estimate for an Euler-factor term: $`\|\chi(p)\, p^{-s}\| \le p^{-\mathrm{Re}\, s}`,
from $`\|\chi\| \le 1` and $`\|p^{-s}\| = p^{-\mathrm{Re}\, s}`. Every sharper bound and every
summability statement about the Euler factors is a refinement of this one inequality.
:::

:::declNotes "A362583.rpow_neg_le_two_rpow_neg"
Base monotonicity of the negative real power: for $`\sigma \ge 0`, $`p^{-\sigma} \le 2^{-\sigma}`,
since $`p \ge 2` and a larger base shrinks a nonpositive exponent. It reduces prime-indexed
Euler-factor bounds to the worst case $`p = 2`, feeding the uniform $`3/4` and $`1/2` bounds.
:::

:::declNotes "A362583.two_rpow_neg_half_le"
The crude numeric estimate $`2^{-1/2} \le 3/4`. It is the base-case constant behind the
geometric-tail bound for the layer $`T`: combined with base monotonicity it yields
$`\|z_p\| \le 3/4 < 1` on the half-plane, so the per-prime series converge.
:::

:::declNotes "A362583.norm_χ_mul_cpow_le_three_quarters"
On the half-plane $`\mathrm{Re}\, s \ge 1/2`, the Euler-factor term is bounded by $`3/4`:
$`\|\chi(p)\, p^{-s}\| \le 3/4`. Keeping $`\|z_p\|` strictly below $`1` is what makes the
geometric tail $`t_p` converge, and gives the constant $`(1 - \|z_p\|)^{-1} \le 4` used in
`norm_tp_le` and in the holomorphy $`M`-test.
:::

:::declNotes "A362583.norm_χ_mul_cpow_le_half"
On the closed half-plane $`\mathrm{Re}\, s \ge 1`, the Euler-factor term is bounded by $`1/2`:
$`\|\chi(p)\, p^{-s}\| \le 1/2`. This is the estimate that guarantees $`\|z_p\| < 1` on the
domain of the per-prime split `neg_log_split`, so that the logarithm series may be applied
there.
:::

:::declNotes "A362583.norm_χ_mul_cpow_le_rpow_neg_half"
On $`\mathrm{Re}\, s \ge 1/2`, the Euler-factor term obeys the prime-decaying bound
$`\|\chi(p)\, p^{-s}\| \le p^{-1/2}`. Cubing this decay yields the summable $`p^{-3/2}` per-prime
bound in `norm_tp_le` — the input to $`T`'s uniform bound $`C_T` and its holomorphy.
:::

:::declNotes "A362583.neg_two_mul_re"
A real-part bookkeeping identity: $`\mathrm{Re}\bigl(-(2s)\bigr) = -2\,\mathrm{Re}\, s`. It lets
$`\|p^{-(2s)}\|` be rewritten as $`p^{-2\,\mathrm{Re}\, s}` throughout the summability and
holomorphy arguments for the $`k = 2` layer $`B`.
:::

:::declNotes "A362583.neg_log_one_sub_eq_tsum"
The shifted `tsum` form of the logarithm series: for $`\|z\| \le 1/2`,
$$`-\operatorname{Log}(1 - z) \;=\; \sum_{k \ge 0} \frac{z^{k+1}}{k+1}.`
It is the reindexed companion of the `HasSum` version, starting the sum at $`k = 0` (so the
vanishing $`k = 0` term of the raw Taylor series is dropped) — the shape the peeling argument in
`neg_log_split` consumes.
:::

:::declNotes "A362583.tpReal"
The real companion of the per-prime $`k \ge 3` tail: with real powers and the integer kernel
$`\kappa(p)` in place of $`\chi(p)`,
$$`t_p(\sigma) \;=\; \sum_{k \ge 0} \frac{\bigl(\kappa(p)\, p^{-\sigma}\bigr)^{k+3}}{k+3}.`
It is the real-axis form of $`t_p`, agreeing with the complex tail at real arguments
(`tp_ofReal`) and summing to the real layer $`T(\sigma)`.
:::

:::declNotes "A362583.layerTReal"
The real companion of the $`k \ge 3` layer, summed over all primes:
$$`T(\sigma) \;=\; \sum_p t_p(\sigma).`
This is the real-axis form of $`T` that the endgame evaluates; it is bounded in absolute value
by $`C_T` for $`\sigma \ge 1/2` (`abs_layerTReal_le`).
:::

:::declNotes "A362583.C_B"
The explicit finite constant bounding the $`k = 2` layer for real $`\sigma \ge 1`:
$$`C_B \;=\; \tfrac12 \sum_p p^{-2}.`
It is finite by summability of $`\sum_p p^{-2}` and serves as the uniform cap $`B(\sigma) \le C_B`
(`layerBReal_le_C_B`) — the controlled behaviour of $`B` on $`\sigma \ge 1`, complementing its
blow-up as $`\sigma \downarrow 1/2`.
:::

:::declNotes "A362583.C_T"
The explicit uniform bound for the $`k \ge 3` layer on $`\mathrm{Re}\, s \ge 1/2`:
$$`C_T \;=\; \tfrac43 \sum_p p^{-3/2}.`
It is a deliberately crude constant (a $`\kappa \le 4` version of the geometric-tail estimate),
finite by summability of $`\sum_p p^{-3/2}`, and it caps $`\|T(s)\|` across the whole half-plane
(`norm_layerT_le`) — the fact that makes $`T` the tame part of the decomposition.
:::

:::declNotes "A362583.exists_finset_gt_of_not_summable"
The abstract engine of the divergence transfer: if a nonnegative family $`f` over the primes is
not summable, then for every $`M` some *finite* subset $`F` has $`\sum_{p \in F} f(p) > M`.
Non-summability of nonnegative terms means unbounded finite subsums; instantiated at
$`f(p) = 1/p` (and its odd-prime variant) it converts the divergence of $`\sum_p 1/p` into
concrete finite witnesses.
:::

:::declNotes "A362583.not_summable_one_div_odd"
The reciprocal sum over the *odd* primes still diverges: $`\sum_p \bigl[p \ne 2\bigr]/p` is not
summable (dropping the single $`p = 2` term cannot restore convergence). Because the layer $`B`
runs over odd primes only, this odd-prime divergence is exactly what feeds the $`B`-blow-up
`exists_layerBReal_gt`.
:::

:::declNotes "A362583.exists_odd_finset_one_div_gt"
Packages the odd-prime divergence into finite witnesses: for every $`M` there is a finite set
$`F` of primes, all $`\ne 2`, with $`\sum_{p \in F} 1/p > M`. It supplies the finite sets of odd
primes that the divergence transfer at $`s \downarrow 1/2` (`exists_layerBReal_gt`) evaluates.
:::

:::declNotes "A362583.exists_right_of_sum_rpow_gt"
The continuity-padding step: given a finite prime set $`F` and reals $`a, u_0, M` with
$`\sum_{p \in F} p^{-a u_0} > M`, for any $`\eta > 0` there is $`u \in (u_0, u_0 + \eta)` with
$`\sum_{p \in F} p^{-a u} > M`. Since the finite sum is continuous in the exponent, a strict
inequality at the boundary point persists just to its right — the move (used in both divergence
theorems) from the edge $`\sigma = 1` or $`\sigma = 1/2` into the open half-plane where the full
series converges.
:::

:::declNotes "A362583.summable_layerBReal_term"
Convergence of the real $`k = 2` integrand for $`\sigma > 1/2`:
$`\sum_p \bigl[p \ne 2\bigr]\, p^{-2\sigma}` is summable (dominated by $`\sum_p p^{-2\sigma}` with
$`2\sigma > 1`). It makes $`B(\sigma)` well-defined for $`\sigma > 1/2`, and it is what lets the
finite odd-prime subsums be compared to the full series in the blow-up argument.
:::

:::declNotes "A362583.summable_layerB_term"
Convergence of the complex $`k = 2` integrand for $`\mathrm{Re}\, s > 1/2`:
$`\sum_p \bigl[p \ne 2\bigr]\, p^{-(2s)}` is summable, its norms dominated by
$`p^{-2\,\mathrm{Re}\, s}`. This is the well-definedness of the complex layer $`B(s)` on the open
half-plane $`\Omega`.
:::

:::declNotes "A362583.norm_tsum_pow_add_three_div_le"
The abstract geometric-tail bound behind $`t_p`: for $`\|z\| < 1`,
$$`\Bigl\| \sum_{k \ge 0} \frac{z^{k+3}}{k+3} \Bigr\| \;\le\; \frac{\|z\|^3\,(1 - \|z\|)^{-1}}{3}.`
Each term is dominated by $`\|z\|^{k+3}/3` (since $`1/(k+3) \le 1/3`), and the resulting geometric
series sums in closed form. Applied with $`z = z_p` it yields the per-prime bound `norm_tp_le`.
:::

:::declNotes "A362583.norm_tp_le"
The per-prime bound on the $`k \ge 3` tail: on $`\mathrm{Re}\, s \ge 1/2`,
$`\|t_p(s)\| \le \tfrac43 p^{-3/2}`. It combines $`\|z_p\| \le p^{-1/2} \le 2^{-1/2} \le 3/4`
(giving $`(1 - \|z_p\|)^{-1} \le 4`) with the geometric-tail estimate, and it is the summable
majorant driving both $`T`'s uniform bound $`C_T` and its holomorphy via the Weierstrass
$`M`-test.
:::

:::declNotes "A362583.summable_norm_tp"
Absolute summability of the tail over primes: on $`\mathrm{Re}\, s \ge 1/2`,
$`\sum_p \|t_p(s)\|` converges (dominated by $`\tfrac43 \sum_p p^{-3/2}`). It is what lets
$`T = \sum_p t_p` be summed and passed through $`\|\sum_p t_p\| \le \sum_p \|t_p\|` in the bound
`norm_layerT_le`.
:::

:::declNotes "A362583.summable_tp"
Plain summability of the $`k \ge 3` integrand: on $`\mathrm{Re}\, s \ge 1/2`,
$`\sum_p t_p(s)` converges (it is absolutely summable). This is the well-definedness of the layer
$`T(s)` on the half-plane, obtained from the absolute version.
:::

:::declNotes "A362583.norm_layerT_le"
The uniform bound on the $`k \ge 3` layer: $`\|T(s)\| \le C_T` on $`\mathrm{Re}\, s \ge 1/2`,
obtained by summing the per-prime bounds $`\tfrac43 p^{-3/2}`. This uniform control of $`T` across
the whole strip is one half of the decomposition's payoff — $`T` stays bounded while $`B` blows
up, so the divergence in the endgame is carried entirely by $`B`.
:::

:::declNotes "A362583.C_B_nonneg"
Positivity of the layer-$`B` constant: $`0 \le C_B`. A small structural fact used to keep the
inequalities around $`B(\sigma) \le C_B` sign-correct.
:::

:::declNotes "A362583.C_T_nonneg"
Positivity of the layer-$`T` constant: $`0 \le C_T`. Used to keep the norm inequalities involving
the uniform bound on $`T` sign-correct.
:::

:::declNotes "A362583.layerBReal_nonneg"
The real $`k = 2` layer is nonnegative for every $`\sigma`: $`0 \le B(\sigma)`, unconditionally.
The bound holds even below $`1/2`, where the defining series is not summable and its `tsum` is
$`0` by convention. This sign is what lets the blow-up of $`B` force a contradiction in the
endgame, and it lets `norm_layerB_le` pass through the absolute value.
:::

:::declNotes "A362583.layerBReal_le_C_B"
The upper bound on the real $`k = 2` layer: $`B(\sigma) \le C_B` for real $`\sigma \ge 1`,
comparing termwise against $`\tfrac12 \sum_p p^{-2}`. It is the controlled side of $`B`'s
behaviour — bounded for $`\sigma \ge 1`, in contrast to its divergence as $`\sigma \downarrow
1/2`.
:::

:::declNotes "A362583.layerB_ofReal"
Real-axis agreement for the $`k = 2` layer: at a real argument the complex layer is the cast of
its real companion, $`B(\sigma) = (\,B(\sigma)\ \text{real}\,)` in $`\C`, unconditionally. This
identity is what makes the analytic $`B(s)` and the endgame's real $`B(\sigma)` the same object.
:::

:::declNotes "A362583.tp_ofReal"
Real-axis agreement for the per-prime tail: at a real argument $`t_p(\sigma)` is the cast of the
real companion $`t_p(\sigma)` (real), unconditionally, via the character–kernel bridge
$`\chi(p) = \kappa(p)`. Summed over primes it gives the real-axis agreement for the layer $`T`.
:::

:::declNotes "A362583.layerT_ofReal"
Real-axis agreement for the $`k \ge 3` layer: at a real argument $`T(\sigma)` is the cast of its
real companion, unconditionally, by summing `tp_ofReal` over primes. It is the identity behind the
real-companion bound `abs_layerTReal_le`.
:::

:::declNotes "A362583.layerB_im"
On the real axis the $`k = 2` layer is real: $`\operatorname{Im} B(\sigma) = 0` for real
$`\sigma`. A direct consequence of the real-axis agreement `layerB_ofReal`, letting the endgame
work with $`B` as a real quantity.
:::

:::declNotes "A362583.layerB_re"
On the real axis the real part of the $`k = 2` layer is its real companion:
$`\operatorname{Re} B(\sigma) = B(\sigma)` (real), for real $`\sigma`. It extracts the real content
of the complex layer that the endgame actually manipulates.
:::

:::declNotes "A362583.layerB_re_nonneg"
The real part of the $`k = 2` layer is nonnegative on the real axis:
$`0 \le \operatorname{Re} B(\sigma)`. It combines `layerB_re` with `layerBReal_nonneg` and is the
sign fact used where the real part of $`B` enters an inequality.
:::

:::declNotes "A362583.layerT_im"
On the real axis the $`k \ge 3` layer is real: $`\operatorname{Im} T(\sigma) = 0` for real
$`\sigma`. It follows from `layerT_ofReal` and lets $`T` be treated as a real quantity on the
real axis.
:::

:::declNotes "A362583.layerT_re"
On the real axis the real part of the $`k \ge 3` layer is its real companion:
$`\operatorname{Re} T(\sigma) = T(\sigma)` (real), for real $`\sigma`. It exposes the real content
of $`T` used alongside the real $`B` in the endgame.
:::

:::declNotes "A362583.norm_layerB_le"
The complex-norm bound on the $`k = 2` layer: $`\|B(\sigma)\| \le C_B` for real $`\sigma \ge 1`,
the complex form of `layerBReal_le_C_B` obtained by pushing the real bound through the real-axis
agreement and the nonnegativity of $`B`. It caps $`B` on $`\sigma \ge 1` in the norm the analytic
identity uses.
:::

:::declNotes "A362583.abs_layerTReal_le"
The real-companion uniform bound on the $`k \ge 3` layer: $`|T(\sigma)| \le C_T` for real
$`\sigma \ge 1/2`, transported from the complex bound `norm_layerT_le` through `layerT_ofReal`.
This is the form the endgame uses: $`T` stays bounded by a fixed constant while $`B` diverges.
:::

:::declNotes "A362583.differentiableOn_tp"
Each per-prime tail is holomorphic on $`\Omega = \{\mathrm{Re}\, s > 1/2\}`. The proof is a local
$`M`-test with the uniform geometric majorant $`(3/4)^k`, valid on all of $`\Omega`. Holomorphy of
the summands is the input the Weierstrass $`M`-test needs to conclude holomorphy of the layer
$`T`.
:::

:::declNotes "A362583.differentiableOn_layerT"
The $`k \ge 3` layer is holomorphic on $`\Omega = \{\mathrm{Re}\, s > 1/2\}`, by the Weierstrass
$`M`-test with the summable majorant $`M_p = \tfrac43 p^{-3/2}` valid on all of $`\Omega`.
Holomorphy of $`T` on the strip is one of the analytic ingredients of the identity
$`\exp(\text{layers}) = L`-function.
:::

:::declNotes "A362583.differentiableOn_layerB_aux"
Auxiliary holomorphy for the $`k = 2` layer: for each $`\delta > 1/2`, $`B` is holomorphic on the
shifted half-plane $`\{\mathrm{Re}\, s > \delta\}`, by the $`M`-test with the summable bound
$`p^{-2\delta}` (uniform there, but not on all of $`\Omega`). It is the local step assembled by
compact exhaustion into full holomorphy on $`\Omega`.
:::

:::declNotes "A362583.differentiableOn_layerB"
The $`k = 2` layer is holomorphic on $`\Omega = \{\mathrm{Re}\, s > 1/2\}`. Because no single
summable majorant exists on all of $`\Omega`, this goes through a compact-exhaustion / local
$`M`-test route: around each $`s_0 \in \Omega` one works on $`\{\mathrm{Re}\, s > \delta\}` with
$`\delta = (1/2 + \mathrm{Re}\, s_0)/2`. Holomorphy of $`B` on the strip is the other analytic
ingredient of the layer/L-function identity.
:::

:::declNotes "A362583.tsum_term_two_eq_layerB"
Summing the $`k = 2` terms over primes reproduces the layer $`B` exactly:
$`\sum_p \tfrac12\, \chi(p)^2\, p^{-(2s)} = B(s)`, unconditionally, via $`\chi(p)^2 = 1` for odd
$`p` and $`0` at $`p = 2`. It identifies the second layer of the Euler-product logarithm with
$`B` — the piece that carries the divergence — as the per-prime split is summed over primes in the
next chapter.
:::

:::declNotes "A362583.summable_norm_term_one"
Absolute summability of the $`k = 1` (race-carrying) terms for $`\mathrm{Re}\, s > 1`:
$`\sum_p \|\chi(p)\, p^{-s}\|` converges, dominated by $`\sum_p p^{-\mathrm{Re}\, s}`. It is what
lets the leading terms of the per-prime split be summed over primes when assembling the Euler
product.
:::

:::declNotes "A362583.summable_norm_term_two"
Absolute summability of the $`k = 2` terms for $`\mathrm{Re}\, s > 1/2`:
$`\sum_p \bigl\| \tfrac12\, \chi(p)^2\, p^{-(2s)} \bigr\|` converges, dominated by
$`\tfrac12 \sum_p p^{-2\,\mathrm{Re}\, s}`. With the $`k = 1` and tail summabilities it makes the
per-prime split summable term-by-term over primes, so the three layers may be recombined by
linearity.
:::
