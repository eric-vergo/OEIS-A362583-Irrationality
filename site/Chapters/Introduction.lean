/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
A362583 irrationality blueprint — Introduction chapter.

The story: the OEIS A362583 constant encodes the mod-4 residues of the odd primes as
binary digits; the theorem is that this constant is irrational. No nodes here — the
proof DAG starts in the Definitions chapter.
-/

import Verso
import VersoManual
import VersoBlueprint
import Macros
import Bibliography

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true

#doc (Manual) "Introduction" =>

We further the study of the prime race {citep "granville-martin.2006"}[] by encoding the results of the race via an integer sequence,
converting that sequence to an infinite series, and analyzing its convergent value.

In 2023, after watching a Numberphile video on the prime race {citep "numberphile.prime-race"}[], it was
observed that the results of the race could be recorded as a
number sequence, leading to {citet oeis.a362583}[]. After sharing with Tomas Rokicki, he immediately commented that
this naturally leads to a convergent sequence, which ultimately led to this result. We denote that number
$`\varrho`, for "Rokicki's constant". Precisely:

List the odd primes in order and record one binary digit for each: $`b_k = 1`
if the $`k`-th odd prime is congruent to $`3` modulo $`4`, and $`b_k = 0` if it is congruent
to $`1`. Reading the digits as a binary expansion produces *Rokicki's constant* $`\varrho`
$$`\varrho \;=\; 0.10110011\ldots_2 \;=\; \sum_{k \ge 0} b_k\, 2^{-(k+1)} \;\approx\; 0.7004,`


{citet "chebyshev.1853"}[] observed that primes $`\equiv 3 \pmod 4` appear to lead primes $`\equiv 1 \pmod 4`
most of the time, and the race sum $`S(N) = \sum_{p \le N} \chi_4(p)` — where $`\chi_4` is the nonprincipal character mod
$`4`, so each prime $`\equiv 1` scores $`+1` and each prime $`\equiv 3` scores $`-1` — is the
classical measure of that bias. Irrationality of $`\varrho` says the race never settles into an
eventually periodic pattern of leads and deficits: the sequence of residues is, in this
precise sense, aperiodic forever.

The argument combines four main results:

- Both residue classes $`1, 3 \bmod 4` contain infinitely many primes (Dirichlet's theorem {citep "dirichlet.1837"}[] at
  modulus $`4`), so the digit sequence has infinitely many zeros and infinitely many ones.
- If $`\varrho` were rational, its digit sequence would be eventually periodic — a
  self-contained tail-and-pigeonhole argument that avoids any general theory of digit
  expansions.
- Eventually periodic digits force the rigid conclusion $`S(N) = c\,\pi(N) + O(1)` for a
  rational slope $`c`, where $`\pi(N)` counts the primes $`\le N`.
- No such linear race exists: the main analytic theorem, that the mod-4 race sum is never
  $`c\,\pi(N) + O(1)`.

The classical irrationality routes for constants of this kind run through Littlewood's
$`\Omega_\pm`-oscillation for the race {citep "littlewood.1914"}[], or through long runs of consecutive primes in a fixed
class. Neither is needed: refuting the linear trajectory requires only *non-degeneracy* of the race,
not quantitative oscillation. The analytic inputs are exactly five, all present in Mathlib {citep "mathlib.2020"}[]: the analytically continued
Dirichlet $`L`-function $`L(s, \chi_4)`, its nonvanishing at $`s = 1`, the exponential form of
the Euler product, the divergence of $`\sum_p 1/p`, and the identity theorem for holomorphic
functions. No prime number theorem, no PNT in arithmetic progressions, no zero-free regions,
no functional equation.
