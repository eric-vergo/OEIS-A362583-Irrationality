/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
A362583 irrationality blueprint — bibliography.
-/

import VersoManual.Bibliography
import VersoBlueprint.Cite

open Verso.Genre.Manual.Bibliography

@[bib "oeis.a362583"]
def oeis.a362583 : Citable := .inProceedings
    { title := inlines!"Sequence A362583"
    , authors := #[inlines!"Eric Vergo"]
    , year := 2023
    , booktitle := inlines!"The On-Line Encyclopedia of Integer Sequences"
    , url := some "https://oeis.org/A362583"
    }
