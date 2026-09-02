/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
A362583 irrationality blueprint — top-level document, and the source of `index.html`.

The landing page is written here.  Its prose is the paragraph between the
`{blueprint_dashboard …}` block and the first `{include …}` below; the blocks around it
are generated surfaces (the dashboard's trust strip and featured node cards above, the
chapters and the graph/summary/trust pages below), so that paragraph is the only part of
the page authored by hand, and this is the only file it is written in.

Ordinary Verso markup works there, including references that resolve against the rest of
the document instead of being retyped: `{bpref "def:rho"}[…]` for a blueprint node,
`{citep "label"}[]` for a bibliography entry from `Bibliography.lean`, and a plain
`[text](url)` link.  Note that Verso document syntax has no line comments — `--` inside
the document body renders as text — so notes like this one belong up here.

Off-origin *assets* must not be added to the page (an embedded player, a remote image or
script): the site is offline / self-contained and ships a `default-src 'self'`
content-security policy, which blocks them.  Link out and cite instead.
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

{blueprint_dashboard (featured := "def:rho, thm:irrational")}

List the odd primes in order and record one binary digit for each: $`b_k = 1` if the $`k`-th
odd prime is congruent to $`3` modulo $`4`, and $`b_k = 0` if it is congruent to $`1`. Reading
those digits as a binary expansion gives {bpref "def:rho"}[Rokicki's constant $`\varrho`]

$$`\varrho \;=\; 0.10110011\ldots_2 \;=\; \sum_{k \ge 0} b_k\, 2^{-(k+1)} \;\approx\; 0.7004.`

Those digits record the mod-4 prime race, measured by $`S(N) = \sum_{p \le N} \chi_4(p)`, where
$`\chi_4` is the nonprincipal character mod $`4`. {bpref "thm:irrational"}[The main theorem] is
that $`\varrho` is irrational, so its digits are not eventually periodic and the race never
settles into a repeating pattern of leads and deficits.

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

{blueprint_trust_model}

{blueprint_bibliography}
