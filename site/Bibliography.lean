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

/-! ## Sources for the mathematical claims made in the prose -/

/-- Chebyshev's 1853 letter to Fuss: the first record of the bias toward primes
`≡ 3 (mod 4)` that the race sum measures. -/
@[bib "chebyshev.1853"]
def chebyshev.letter1853 : Citable := .article
    { title := inlines!"Lettre de M. le professeur Tchébychev à M. Fuss, sur un nouveau théorème relatif aux nombres premiers contenus dans les formes 4n+1 et 4n+3"
    , authors := #[inlines!"P. L. Chebyshev"]
    , journal := inlines!"Bulletin de la Classe physico-mathématique de l'Académie Impériale des Sciences de Saint-Pétersbourg"
    , year := 1853
    , month := none
    , volume := inlines!"11"
    , number := .concat #[]
    }

/-- Dirichlet's theorem on primes in arithmetic progressions. -/
@[bib "dirichlet.1837"]
def dirichlet.progressions1837 : Citable := .article
    { title := inlines!"Beweis des Satzes, dass jede unbegrenzte arithmetische Progression, deren erstes Glied und Differenz ganze Zahlen ohne gemeinschaftlichen Factor sind, unendlich viele Primzahlen enthält"
    , authors := #[inlines!"P. G. L. Dirichlet"]
    , journal := inlines!"Abhandlungen der Königlich Preußischen Akademie der Wissenschaften"
    , year := 1837
    , month := none
    , volume := .concat #[]
    , number := .concat #[]
    , pages := some (45, 81)
    }

/-- Littlewood's oscillation theorem for the race: the sign of `S(N)` changes
infinitely often. -/
@[bib "littlewood.1914"]
def littlewood.oscillation1914 : Citable := .article
    { title := inlines!"Sur la distribution des nombres premiers"
    , authors := #[inlines!"J. E. Littlewood"]
    , journal := inlines!"Comptes Rendus de l'Académie des Sciences, Paris"
    , year := 1914
    , month := none
    , volume := inlines!"158"
    , number := .concat #[]
    , pages := some (1869, 1872)
    }

/-- The prime-square term as the source of Chebyshev's bias. -/
@[bib "rubinstein-sarnak.1994"]
def rubinsteinSarnak.bias1994 : Citable := .article
    { title := inlines!"Chebyshev's bias"
    , authors := #[inlines!"Michael Rubinstein", inlines!"Peter Sarnak"]
    , journal := inlines!"Experimental Mathematics"
    , year := 1994
    , month := none
    , volume := inlines!"3"
    , number := inlines!"3"
    , pages := some (173, 197)
    , url := some "https://doi.org/10.1080/10586458.1994.10504289"
    }

/-- The standard expository account of prime number races. -/
@[bib "granville-martin.2006"]
def granvilleMartin.races2006 : Citable := .article
    { title := inlines!"Prime number races"
    , authors := #[inlines!"Andrew Granville", inlines!"Greg Martin"]
    , journal := inlines!"American Mathematical Monthly"
    , year := 2006
    , month := none
    , volume := inlines!"113"
    , number := inlines!"1"
    , pages := some (1, 33)
    , url := some "https://doi.org/10.1080/00029890.2006.11920275"
    }

/-- Mathlib, the source of every analytic input the proof consumes. -/
@[bib "mathlib.2020"]
def mathlib.cpp2020 : Citable := .inProceedings
    { title := inlines!"The Lean mathematical library"
    , authors := #[inlines!"mathlib"]
    , year := 2020
    , booktitle := inlines!"Proceedings of the 9th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2020)"
    , url := some "https://doi.org/10.1145/3372885.3373824"
    }
