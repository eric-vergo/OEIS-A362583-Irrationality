/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
A362583 irrationality blueprint — top-level document.
-/

import Verso
import VersoManual
import VersoBlueprint
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
import VersoBlueprint.Commands.Bibliography
import VersoBlueprint.Commands.Formalization

import Contents.TeXPrelude
-- Bring the sanity-pin declarations into the environment so the all-declarations
-- registry (`verso.blueprint.graph.includeAllDecls`) tracks every A362583 decl,
-- including the pin-scoped helpers that no blueprint node wires.
import A362583.Pins
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

{blueprint_dashboard}

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

{blueprint_formalization "../formalization.yaml"}

{blueprint_bibliography}
