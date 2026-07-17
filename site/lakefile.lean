/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
import Lake
open Lake DSL

-- `standard-blueprint` branch: this site is built against STOCK upstream
-- `leanprover/verso-blueprint` (default branch `v4.32.0`), NOT the eric-vergo
-- forks used on `main`.  Upstream verso-blueprint transitively brings its own
-- `verso`, `verso-slides`, `subverso`, and `proofwidgets`, so the three fork
-- `require`s (subverso / verso / VersoBlueprint from eric-vergo) are gone.
--
-- Ordering matters for shared transitive deps: upstream verso-blueprint pins
-- `proofwidgets @ v0.0.104` (e4952a) while Mathlib v4.32.0 uses a different
-- `proofwidgets` revision (6e311e, tracked in Mathlib's manifest) — and
-- `lake exe cache get` only computes correct hashes when the project's
-- `proofwidgets` matches Mathlib's.  Per Mathlib's own post-update hook, the fix
-- is to require `mathlib` LAST so its transitive versions take precedence; that
-- overrides verso's `proofwidgets` pin down to Mathlib's revision (verso still
-- compiles against it — the same revision `main` already uses).  Regenerate with
-- a TARGETED `lake update VersoBlueprint` (never a blanket `lake update`, which
-- floats the `@main` deps and can drag the toolchain forward).
require A362583 from ".."
require VersoBlueprint from git "https://github.com/leanprover/verso-blueprint" @ "v4.32.0"
require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.32.0"

package Contents where
  precompileModules := false
  leanOptions := #[
    ⟨`experimental.module, true⟩,
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩,
    ⟨`relaxedAutoImplicit, false⟩,
    ⟨`maxSynthPendingDepth, .ofNat 3⟩,
    -- Blueprint rendering options that upstream v4.32.0 actually defines.
    ⟨`weak.verso.blueprint.math.lint, true⟩,
    ⟨`weak.verso.blueprint.externalCode.strictResolve, true⟩
  ]
  -- Dropped on this branch (fork-only or unsupported upstream):
  --   verso.blueprint.graph.includeAllDecls  (fork extension; upstream lacks it)
  --   verso.blueprint.declNamePrefix          (fork extension)
  --   verso.blueprint.trust.*                 (fork trust/comparator surface)
  --   verso.code.warnLineLength               (fork code-lint tuning)
  --   the `ciRunUrl` config-time env read      (fed the fork comparator page)

@[default_target]
lean_lib Contents where
  roots := #[`Authors, `Contents, `Chapters, `Bibliography, `Macros]

-- No `lean_exe` target on this branch: the upstream project template ships none.
-- Generation runs the entry point through Lake's Lean wrapper
-- (`lake exe vbp build`, which discovers `Main.lean`; or the direct
-- `lake build Contents && lake env lean --run Main.lean --output _out/site`).
