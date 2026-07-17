/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
A362583 irrationality blueprint — top-level document.

`standard-blueprint` branch notes (vs `main`, which uses the eric-vergo forks):
  * The fork homepage `{blueprint_dashboard}` overview widget is a fork-only
    command (upstream v4.32.0 has no dashboard); a short prose intro replaces it.
  * `{blueprint_formalization "../formalization.yaml"}` is a fork-only
    formalization-metadata command (dropped; upstream has no equivalent).
  * `import VersoBlueprint.Commands.Formalization` and `import A362583.Pins`
    (the latter only fed the fork-only `graph.includeAllDecls` all-decls
    registry) are dropped.
  * The `{blueprint_graph}` / `{blueprint_summary}` / `{blueprint_bibliography}`
    blocks are all stock upstream commands and are kept.
-/

import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import VersoBlueprint.Commands.Bibliography
-- NB (standard-blueprint branch): upstream v4.32.0 ships no `Commands.Formalization`
-- command, so the fork's `import VersoBlueprint.Commands.Formalization` and the
-- `A362583.Pins` import (which only fed the fork-only
-- `verso.blueprint.graph.includeAllDecls` all-decls registry) are dropped here.

import Contents.TeXPrelude
import Authors
import Bibliography
import Chapters.Introduction
import Chapters.Definitions
import Chapters.DigitLayer
import Chapters.RaceBookkeeping
import Chapters.BoundedHolomorphy
import Chapters.Layers
import Chapters.EulerProduct
import Chapters.ForcingC
import Chapters.Endgame
import Chapters.MainTheorem

open Verso.Genre
open Verso.Genre.Manual hiding citep citet citehere
open Informal

set_option doc.verso true
set_option verso.blueprint.trimTeXLabelPrefix true

set_option pp.rawOnError true

#doc (Manual) "A362583 Irrationality" =>

%%%
shortTitle := "A362583"
authors := ["Eric Vergo", "Claude Fable 5"]
%%%

This blueprint tracks the `sorry`-free Lean 4 proof that the prime race constant
$`\varrho` is irrational. Its two headline nodes are the definition of
$`\varrho` (label `def:rho`) and the top-level irrationality theorem (label
`thm:irrational`); the dependency graph and progress summary at the foot of this
page give the full picture, and the chapters below build the argument from the
digit layer up.

{include 0 Chapters.Introduction}

{include 0 Chapters.Definitions}

{include 0 Chapters.DigitLayer}

{include 0 Chapters.RaceBookkeeping}

{include 0 Chapters.BoundedHolomorphy}

{include 0 Chapters.Layers}

{include 0 Chapters.EulerProduct}

{include 0 Chapters.ForcingC}

{include 0 Chapters.Endgame}

{include 0 Chapters.MainTheorem}

{blueprint_graph}

{blueprint_summary}

{blueprint_bibliography}
