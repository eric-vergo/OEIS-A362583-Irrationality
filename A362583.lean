/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
import A362583.BoundedHolo
import A362583.CaseNonzero
import A362583.CaseZero
import A362583.Defs
import A362583.DigitLayer
import A362583.EulerLog
import A362583.Layers
import A362583.Main
import A362583.Pins
import A362583.RaceCount

/-!
# A362583 irrationality: library root

Root module for the `A362583` library, importing every module of the
`sorry`-free proof that the prime race constant `ϱ` (the A362583 constant)
is irrational.

The primary deliverable is `A362583.irrational_ϱ` (`A362583/Main.lean`); the
elementary definitions live in `A362583/Defs.lean` and the four proof layers in
`A362583/DigitLayer.lean` (Steps A, B), `A362583/RaceCount.lean` (Step C), and
`A362583/Layers.lean` / `A362583/EulerLog.lean` / `A362583/BoundedHolo.lean` /
`A362583/CaseNonzero.lean` / `A362583/CaseZero.lean` (Step D).  See the module
docstring of each file for details.
-/
