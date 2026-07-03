/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo
-/
import A362583.Defs
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.NumberTheory.Real.Irrational

/-!
# A362583: theorem statements (spec §2, §3)

Remaining theorem/lemma targets of the project, with placeholder proofs pending
the proof phases (each tracked in `SORRIES.md`).  Proved targets move to their
layer files with signatures verbatim (lock preserved; see `git tag statement-lock`):
Steps A–B (`bits_infinite_ones`, `bits_infinite_zeros`,
`eventuallyPeriodic_of_not_irrational`) live in `A362583/DigitLayer.lean`;
Step C (`raceSum_linear_of_eventuallyPeriodic`) lives in `A362583/RaceCount.lean`.
Statements follow the §3
statement-hygiene principle: elementary `if`/`%` arithmetic, `Nat.primeCounting`,
`Irrational`, and the `Defs.lean` objects only.

Proof architecture (spec §2.2): A (infinitude) → B (rational ⇒ bits eventually
periodic) → C (periodic ⇒ linear race) → D (no linear race) → contradiction.
-/

namespace A362583

/-- **Primary deliverable** (spec §2.2): the A362583 constant is irrational. -/
theorem irrational_x : Irrational x := by
  sorry

end A362583
