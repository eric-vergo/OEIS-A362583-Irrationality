/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
import Lake
open Lake DSL

-- Root-level git requires for the three forks, tracking their `blueprint`
-- branches.  The forks require each other from git too, so they build
-- standalone; requiring them HERE as well is what out-ranks verso-slides'
-- transitive pin of the upstream `leanprover/verso` (Lake resolves by NAME and
-- honours the ROOT package's `require`s first), keeping the site on the forks
-- and preserving the offline / self-hosted-`marked` invariant they provide.
-- The resolved commits are recorded in lake-manifest.json; a
-- `lake update subverso verso VersoBlueprint` re-pins to the current
-- `blueprint` HEAD of each fork.
require subverso from git "https://github.com/eric-vergo/subverso.git" @ "blueprint"
require verso from git "https://github.com/eric-vergo/verso.git" @ "blueprint"
require VersoBlueprint from git "https://github.com/eric-vergo/Showcase.git" @ "blueprint"
require A362583 from ".."
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.33.1"

/-- URL of the CI run that produced these checks, read from the `CI_RUN_URL`
environment variable at configuration time.  Empty ⇒ the comparator page falls
back to the `run_url` recorded in `../comparator/comparator-status.json`, which
is the link a reader wants anyway: the run that last *changed* the verdict, not
whichever run happened to regenerate the site.

The shared CI standard deliberately sets `CI_RUN_URL` EMPTY for the site build
(and passes no `-R`): a run id baked into the page made every run's bytes differ,
which cut a release every run.  So this reads as the fallback both locally and in
CI, and stays here for a build that wants to override it. -/
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
    ⟨`weak.verso.blueprint.trust.comparatorStatus, "../comparator/comparator-status.json"⟩,
    ⟨`weak.verso.blueprint.trust.comparatorConfig, "../comparator/comparator.json"⟩,
    ⟨`weak.verso.blueprint.trust.challengeFile, "../comparator/Challenge.lean"⟩,
    ⟨`weak.verso.blueprint.trust.solutionFile, "../comparator/Solution.lean"⟩,
    -- The build-time axiom audit (`Lean.collectAxioms` over every presented
    -- declaration, every registry entry, and every declaration named in
    -- formalization.yaml) is advisory by default: a decl whose closure carries
    -- `sorryAx` or a nonstandard axiom is badged and warned about.  Here it is a
    -- build error instead: the audit is the check behind the `sorry_count: 0` /
    -- standard-axiom declaration in `../formalization.yaml`, so a finding is not
    -- something this site may render around.
    ⟨`weak.verso.blueprint.trust.requireAuditClean, true⟩,
    -- comparator.live project id for the "check this claim yourself" permalinks
    -- on the comparator page: "mathlib-stable" is the toolchain-matched
    -- Lean + Mathlib environment there.  Links only — nothing is fetched at
    -- build time and nothing off-origin is emitted into the site.
    ⟨`weak.verso.blueprint.trust.comparatorLiveProject, "mathlib-stable"⟩,
    ⟨`weak.verso.blueprint.trust.ciRunUrl, ciRunUrl⟩,
    -- The meaning closure of the certified claim (F1): what a reader must read to
    -- know what `Challenge.irrational_ϱ` SAYS, as opposed to how it is proved.
    -- Computed by the fork's `statement-closure` executable in a subprocess that
    -- imports exactly the challenge chain's declared imports — not this site's
    -- environment, where the subject library and Verso are in scope and a short
    -- name could resolve to something the verifier never saw.  The closure is
    -- labelled as bound to the verdict only when the chain it hashed matches, in
    -- order, what the verifying run recorded in the status artifact's
    -- `challenge_chain`; until CI writes that field the surface renders the
    -- honest chain-unbound label, which is the correct thing for it to say.
    -- Probe-and-degrade: an absent or failing tool records the reason instead of
    -- failing the build, so a local build without `lake build «statement-closure»`
    -- still generates.
    ⟨`weak.verso.blueprint.trust.statementClosure, true⟩,
    ⟨`weak.verso.code.warnLineLength, .ofNat 0⟩
  ]

-- The trust surfaces are captured at ELABORATION from these four files, and none
-- of them is a Lean module, so Lake otherwise tracks no read of them: edit only
-- the comparator status, its config, the Challenge or the Solution, rebuild, and
-- a warm `.olean` republishes the entire prior evidence page — old verdict beside
-- the old statement, internally consistent — under the new build's revision
-- (codex-audit CX-075).  An `input_file` hashes each into the library's extra-dep
-- job trace, which Lake mixes into every module's `depTrace`, so an ordinary
-- `lake build Contents` re-elaborates the capture when one of them changes.
--
-- Three things here are load-bearing, per the recipe in the fork's
-- `VersoBlueprint.TrustFreshness` module docs:
--   * `needs`, never `extraDepTargets` — for a named-kind declaration (which
--     `input_file` is) Lake resolves `extraDepTargets` through a branch that
--     neither builds the target nor contributes a trace, i.e. a silent no-op;
--   * `path` is relative to the PACKAGE directory, so this sub-package site
--     writes `../…` exactly as the trust options above do;
--   * `text` stays at its default `false` — `text := true` normalizes line
--     endings before hashing, so a CRLF↔LF change would move the generator's
--     byte digest without moving Lake's trace, giving a build that fails the
--     freshness gate and cannot be fixed by rebuilding.
--
-- This is convenience, not the guarantee: `Informal.TrustFreshness` re-reads and
-- re-digests every recorded input before anything is written, and CI re-runs the
-- same comparison against the checkout.  The edge is what keeps that stop a
-- backstop instead of the workflow.
input_file comparatorStatus where
  path := "../comparator/comparator-status.json"

input_file comparatorConfig where
  path := "../comparator/comparator.json"

input_file comparatorChallenge where
  path := "../comparator/Challenge.lean"

input_file comparatorSolution where
  path := "../comparator/Solution.lean"

@[default_target]
lean_lib Contents where
  needs := #[`@/comparatorStatus, `@/comparatorConfig,
             `@/comparatorChallenge, `@/comparatorSolution]
  roots := #[`Authors, `Contents, `Chapters, `Bibliography, `Macros]

@[default_target]
lean_exe «blueprint-gen» where
  root := `Main
  supportInterpreter := true
