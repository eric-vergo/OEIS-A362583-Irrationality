/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
/-
A362583 irrationality blueprint — site generator entrypoint.

`standard-blueprint` branch: this mirrors the upstream project template's
`ProjectTemplateMain.lean` exactly, calling `blueprintMainWithPreviewData`.
Upstream auto-injects the blueprint HTML assets (including the math / tex-prelude
runtime, per-math-inline via `Inline.bpMath`), so the fork's manual
`htmlAssets` / `renderConfig` wiring and the `blueprintMainWithFeatures` entry
point are dropped here.
-/

import VersoManual
import VersoBlueprint.PreviewManifest
import Contents

open Verso Doc
open Verso.Genre Manual

def main (args : List String) : IO UInt32 :=
  Informal.PreviewManifest.blueprintMainWithPreviewData
    (%doc Contents)
    args
    (extensionImpls := by exact extension_impls%)
