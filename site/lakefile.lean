/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
import Lake
open Lake DSL

-- Root-level git pins for the three forks.  Lake resolves dependencies by NAME
-- and honours the ROOT package's `require`s first, so pinning subverso / verso /
-- VersoBlueprint here shadows every transitive `require` of the same name:
-- verso's own `require subverso from "../subverso"`, verso-blueprint's
-- `require verso from "../verso"` path specs are never materialized, and
-- verso-slides' transitive pin of the upstream `leanprover/verso` is out-ranked.
-- That keeps the site building against these exact commits (instead of whatever
-- sibling working trees happen to be on disk) while preserving the offline /
-- self-hosted-`marked` invariant that the forks provide.
require subverso from git "https://github.com/eric-vergo/subverso.git" @ "62b4fda523e8b367180fac5e3c47a7d0f81dadd4"
require verso from git "https://github.com/eric-vergo/verso.git" @ "8352397591c64bc9d7543aea295330ad5083b140"
require VersoBlueprint from git "https://github.com/eric-vergo/verso-blueprint.git" @ "863c0b72aec904ba3749c82dbe38c325b2276a6d"
require A362583 from ".."
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.31.0"

/-- URL of the CI run that produced these checks, read from the `CI_RUN_URL`
environment variable at configuration time.  Empty on a local build (the env var
is unset) ⇒ the comparator page renders no "View CI run" link, which is the
expected local behaviour.  CI (`.github/workflows/ci.yml`) sets `CI_RUN_URL` to
a step-level deep link into the "Run comparator" step and
passes `-R`/`--reconfigure` on the `lake build Contents` step so this value is
re-read fresh each run — Lake's config trace keys off the lakefile *text* hash
(plus toolchain/platform), not env vars, so without `-R` a warm-cache run would
splice in a stale URL. -/
def ciRunUrl : String :=
  run_io return ((← IO.getEnv "CI_RUN_URL").getD "")

package Contents where
  precompileModules := false
  leanOptions := #[
    ⟨`experimental.module, true⟩,
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    ⟨`weak.verso.blueprint.math.lint, true⟩,
    ⟨`weak.verso.blueprint.externalCode.strictResolve, true⟩,
    ⟨`weak.verso.blueprint.graph.includeAllDecls, true⟩,
    ⟨`weak.verso.blueprint.declNamePrefix, "A362583"⟩,
    ⟨`weak.verso.blueprint.trust.formalizationYaml, "../formalization.yaml"⟩,
    ⟨`weak.verso.blueprint.trust.comparatorStatus, "../comparator-status.json"⟩,
    ⟨`weak.verso.blueprint.trust.comparatorConfig, "../comparator.json"⟩,
    ⟨`weak.verso.blueprint.trust.challengeFile, "../Challenge/Challenge.lean"⟩,
    ⟨`weak.verso.blueprint.trust.solutionFile, "../Solution/Solution.lean"⟩,
    ⟨`weak.verso.blueprint.trust.ciRunUrl, ciRunUrl⟩,
    ⟨`weak.verso.code.warnLineLength, .ofNat 0⟩
  ]

@[default_target]
lean_lib Contents where
  roots := #[`Authors, `Contents, `Chapters, `Bibliography, `Macros]

@[default_target]
lean_exe «blueprint-gen» where
  root := `Main
  supportInterpreter := true
