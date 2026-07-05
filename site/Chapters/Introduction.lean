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

The subject of this blueprint is a single real number. List the odd primes in order —
$`3, 5, 7, 11, 13, 17, 19, 23, \ldots` — and record one binary digit for each: $`b_k = 1`
if the $`k`-th odd prime is congruent to $`3` modulo $`4`, and $`b_k = 0` if it is congruent
to $`1`. Reading the digits as a binary expansion produces the *prime race constant* $`\varrho`, the
constant of {citet oeis.a362583}[],
$$`\varrho \;=\; 0.10110011\ldots_2 \;=\; \sum_{k \ge 0} b_k\, 2^{-(k+1)} \;\approx\; 0.7004,`
and this site documents a complete, sorry-free Lean 4 proof of the theorem that $`\varrho` is
irrational.

The digits of $`\varrho` transcribe the *mod-4 prime race*. Chebyshev observed in 1853 that primes
$`\equiv 3 \pmod 4` appear to lead primes $`\equiv 1 \pmod 4` most of the time, and the race
sum $`S(N) = \sum_{p \le N} \chi_4(p)` — where $`\chi_4` is the nonprincipal character mod
$`4`, so each prime $`\equiv 1` scores $`+1` and each prime $`\equiv 3` scores $`-1` — is the
classical measure of that bias. Irrationality of $`\varrho` says the race never settles into an
eventually periodic pattern of leads and deficits: the sequence of residues is, in this
precise sense, aperiodic forever.

The proof has four layers, assembled by pure logic at the end:

- *Step A.* Both residue classes contain infinitely many primes (Dirichlet's theorem at
  modulus $`4`), so the digit sequence contains infinitely many zeros and infinitely many
  ones.
- *Step B.* If $`\varrho` were rational, its digit sequence would be eventually periodic — a
  self-contained tail-and-pigeonhole argument that avoids any general theory of digit
  expansions.
- *Step C.* Eventually periodic digits force the very rigid conclusion
  $`S(N) = c\,\pi(N) + O(1)` for a rational slope $`c`, where $`\pi(N)` counts primes
  $`\le N`.
- *Step D.* No such linear race exists — the main analytic theorem, and the heart of the
  formalization.

The design choice behind Step D is what makes the project feasible. The classical
irrationality routes for constants of this kind run through Littlewood's 1914
$`\Omega_\pm`-oscillation for the race, or through long runs of consecutive primes in a fixed
class — both far beyond current formalization technology. Neither is needed: refuting the
rigid conclusion of Step C requires only *non-degeneracy* of the race, not quantitative
oscillation. The analytic inputs consumed by Step D are exactly five, all present in Mathlib:
the analytically continued Dirichlet $`L`-function $`L(s, \chi_4)`, its nonvanishing at
$`s = 1`, the exponential form of the Euler product, the divergence of $`\sum_p 1/p`, and the
identity theorem for holomorphic functions. No prime number theorem, no PNT in arithmetic
progressions, no zero-free regions, no functional equation.

A statement-hygiene principle governs the Lean development: the four definitions, the
irrationality theorem, and the analytic core it rests on mention only elementary objects — the $`k`-th prime, remainder arithmetic,
finite sums, and one geometric-type series — so a reader can audit *what was proved* without
trusting any of the analytic machinery, which is confined to proofs. The chapters that follow
narrate the full argument — Steps A through D and their supporting lemmas — in the same order
the Lean sources prove it.
