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
require verso from git "https://github.com/eric-vergo/verso.git" @ "8267a4b5041e123ca6f017bd20acdca9b2b92c04"
require VersoBlueprint from git "https://github.com/eric-vergo/verso-blueprint.git" @ "6d8fcf4cd0d5a627e98902f2662097ddb308774e"
require A362583 from ".."
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.31.0"

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
    ⟨`weak.verso.code.warnLineLength, .ofNat 0⟩
  ]

@[default_target]
lean_lib Contents where
  roots := #[`Authors, `Contents, `Chapters, `Bibliography, `Macros]

@[default_target]
lean_exe «blueprint-gen» where
  root := `Main
  supportInterpreter := true
