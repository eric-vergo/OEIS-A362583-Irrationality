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
require verso from git "https://github.com/eric-vergo/verso.git" @ "128e6d844a8ae57abb0bc19b7f64e1887429c4a2"
require VersoBlueprint from git "https://github.com/eric-vergo/verso-blueprint.git" @ "9ea1e9e1ed4998c6cb685c4fbffe2919466e449b"
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
