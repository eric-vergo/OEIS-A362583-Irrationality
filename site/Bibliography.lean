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

/-- The Numberphile video whose prime-race discussion prompted the sequence.

Recorded as an `inProceedings` entry: `Citable` has no video constructor, and this
is the closest fit that carries a venue (the channel) alongside a title, a year and
a URL.  The link goes out to YouTube; nothing off-origin is embedded in the page,
which would break the site's offline / self-contained invariant and its
`default-src 'self'` content-security policy. -/
@[bib "numberphile.prime-race"]
def numberphile.primeRace : Citable := .inProceedings
    { title := inlines!"The Prime Number Race (with 3Blue1Brown)"
    , authors := #[inlines!"Brady Haran", inlines!"Grant Sanderson"]
    , year := 2023
    , booktitle := inlines!"Numberphile"
    , url := some "https://www.youtube.com/watch?v=YAsHGOwB408"
    }
