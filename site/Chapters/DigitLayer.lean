/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
A362583 irrationality blueprint — Digit Layer chapter.

Steps A and B: both residue classes are infinite, and a rational x would have eventually
periodic bits.
-/

import Verso
import VersoManual
import VersoBlueprint
import Macros
import Bibliography
import A362583.DigitLayer

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true
set_option pp.rawOnError true

#doc (Manual) "The Digit Layer" =>

:::group "digit"
Step A: the digit sequence has infinitely many ones and infinitely many zeros. Step B: if the
constant were rational, its digits would be eventually periodic.
:::

This chapter contains all the digit-level arithmetic of the proof. Step A is the only place
Dirichlet's theorem on primes in arithmetic progressions enters; Step B is a self-contained
binary-tail argument that deliberately dodges any general "rational iff eventually periodic
digits" library, which Mathlib does not currently have.

:::theorem "thm:bits-ones" (lean := "A362583.bits_infinite_ones") (parent := "digit") (uses := "def:bit")
The set $`\{k \mid b_k = 1\}` is infinite.
:::

:::proof "thm:bits-ones"
By Dirichlet's theorem at modulus $`4` — in Mathlib's form, the primes $`\equiv 3 \pmod 4`
form an infinite set — infinitely many primes lie in the class $`3 \bmod 4`. These transfer to
bit indices along the injection sending a prime $`p` to the number of primes below $`p`, minus
one; its inverse is the odd-prime enumeration $`k \mapsto p_k`, and $`2` is excluded since
$`2 \not\equiv 3 \pmod 4`. So infinitely many indices $`k` have $`p_k \equiv 3 \pmod 4`, i.e.
$`b_k = 1`. $`\blacksquare`
:::

:::theorem "thm:bits-zeros" (lean := "A362583.bits_infinite_zeros") (parent := "digit") (uses := "def:bit")
The set $`\{k \mid b_k = 0\}` is infinite. Together with the previous theorem this is Step A:
the digit sequence is neither eventually all ones nor eventually all zeros, which is exactly
what Step B needs to keep the binary tails strictly between $`0` and $`1`.
:::

:::proof "thm:bits-zeros"
The same argument as the previous theorem, applied to the residue class $`1 \bmod 4`:
Dirichlet's theorem supplies infinitely many primes $`\equiv 1 \pmod 4`, the odd-prime
enumeration injects them into the index set, and for such an index $`k`, $`p_k \equiv 1 \pmod 4`
is in particular $`\not\equiv 3 \pmod 4`, so $`b_k = 0`. $`\blacksquare`
:::

:::theorem "thm:eventually-periodic" (lean := "A362583.eventuallyPeriodic_of_not_irrational") (parent := "digit") (uses := "def:x, thm:bits-ones, thm:bits-zeros")
*Step B.* If $`x` is not irrational, then the bit sequence is eventually periodic: there
exist $`N` and $`P > 0` with $`b_{k+P} = b_k` for all $`k \ge N`.
:::

:::proof "thm:eventually-periodic"
Define the binary tails $`t_k := \sum_{j \ge 0} b_{k+j}\, 2^{-(j+1)}`, so that $`t_0 = x`.
The five steps B1–B5 below follow the Lean file's zero-based indexing.

*(B1)* $`t_k \in (0,1)` *strictly*, for every $`k`: infinitely many later ones
(Step A) force $`t_k > 0`, and infinitely many later zeros force $`t_k < 1`.

*(B2)* The recurrence $`t_k = (b_k + t_{k+1})/2` holds by splitting off the first term of
the tail. Combined with B1: if $`b_k = 1` then $`t_k \in (1/2, 1)`; if $`b_k = 0` then
$`t_k \in (0, 1/2)`. In particular $`t_k \ne 1/2` always, so $`t_k` *determines* $`b_k`
($`b_k = 1 \iff t_k > 1/2`) and hence also $`t_{k+1} = 2 t_k - b_k`.

*(B3)* $`2^k x` is an integer plus $`t_k`, and $`t_k \in (0,1)`, so
$`t_k = \operatorname{fract}(2^k x)`.

*(B4)* If $`x` is rational with denominator $`b`, then each
$`t_k = \operatorname{fract}(2^k x)` lies in the finite set
$`\{0, 1/b, \ldots, (b-1)/b\}` — in Lean, the denominator of the rational witness produced
by unfolding "not irrational". By the pigeonhole principle there are $`m < n` with
$`t_m = t_n`.

*(B5)* Since $`t_k` determines both $`b_k` and $`t_{k+1}` (B2), induction propagates the
collision: $`t_{m+i} = t_{n+i}` and $`b_{m+i} = b_{n+i}` for all $`i \ge 0`. So the bits are
periodic with period $`P = n - m` from index $`m`. $`\blacksquare`
:::
