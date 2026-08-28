/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
import Lean.Elab.Command
import A362583

/-!
# Comparator sandbox regression fixture (CI only)

`comparator/Solution.lean` with one addition: a top-level `run_cmd` that tries to
write files outside the comparator's Landlock sandbox, before any declaration of
this module is elaborated.  Lean elaboration is arbitrary code execution, so a
comparator run that elaborates the solution *outside* confinement lets that write
succeed — the failure recorded as CX-012, where the workspace prebuilt
`Challenge` and `Solution` and the sandboxed `lake build` was left a no-op.

The fixture is driven by `comparator/comparator-probe.json` from the
"Denied-write probe" step of `.github/workflows/ci.yml`, and it is expected to
FAIL:

* every write denied — elaboration aborts with the sentinel
  `COMPARATOR_PROBE_WRITES_DENIED`, the sandboxed `lake build` fails and the
  comparator exits non-zero.  This is the passing outcome; CI matches the
  sentinel so that an unrelated failure cannot be mistaken for it.
* any write accepted — this module stays silent, proves the challenge statement
  like the real solution, and the comparator exits 0 with the canary files on
  disk.  CI fails on both signals.

It is registered as the `SolutionProbe` lake lib but is deliberately not a
default target and nothing imports it: built outside the sandbox it writes
exactly the canary files it exists to prove impossible.
-/

namespace SolutionProbe

/-- The paths the probe writes to.  Both parent directories always exist, so a
refused write is a denial rather than a missing directory: the process working
directory, which is inside the repository checkout the sandbox mounts read-only
(next to the comparator config, the challenge sources and the checked-out tool),
and the home directory, outside the checkout, where the landrun and nanoda
binaries live. -/
private def probeTargets : IO (Array String) := do
  let cwd ← IO.currentDir
  let mut targets : Array String := #[cwd.toString ++ "/comparator-probe-canary"]
  if let some home := (← IO.getEnv "HOME") then
    targets := targets.push (home ++ "/comparator-probe-canary")
  return targets

/-- Attempt one write, reporting whether it was accepted. -/
private def tryWrite (target : String) : IO Bool := do
  try
    IO.FS.writeFile (System.FilePath.mk target)
      "comparator sandbox breach: an elaboration-time write succeeded\n"
    return true
  catch _ =>
    return false

/-- The targets whose writes were accepted; empty means the sandbox held. -/
private def attemptEscape (targets : Array String) : IO (Array String) := do
  let mut written : Array String := #[]
  for target in targets do
    if (← tryWrite target) then
      written := written.push target
  return written

end SolutionProbe

run_cmd do
  let targets ← SolutionProbe.probeTargets
  let written ← SolutionProbe.attemptEscape targets
  if written.isEmpty then
    let names := String.intercalate ", " targets.toList
    throwError "COMPARATOR_PROBE_WRITES_DENIED: every elaboration-time write outside the sandbox was refused (tried: {names})"

namespace Challenge

/-- The `k`-th odd prime: `oddPrime 0 = 3`, `oddPrime 1 = 5`, `oddPrime 2 = 7`, ….
Writing the odd primes as `p_1, p_2, …`, this is `p_{k+1}`; since
`Nat.nth Nat.Prime 0 = 2`, skipping index 0 skips exactly the prime 2. -/
noncomputable def oddPrime (k : ℕ) : ℕ := Nat.nth Nat.Prime (k + 1)

/-- `k`-th bit of the constant: `1` iff the `k`-th odd prime is `≡ 3 (mod 4)`.
The `b_{k+1}` of the 1-based bit sequence; first values `1 0 1 1 0 0 1 1`
(primes `3, 5, 7, 11, 13, 17, 19, 23`). -/
noncomputable def bit (k : ℕ) : ℕ := if oddPrime k % 4 = 3 then 1 else 0

/-- Rokicki's constant (the A362583 constant): the sum of the series
`ϱ = Σ_{k ≥ 0} bit k · 2^{-(k+1)}`, i.e. the real number whose `k`-th binary digit is
`bit k` — in binary `0.b₀b₁b₂…₂ ≈ 0.7004001…` (decimal). OEIS A362583 lists the
successive digit prefixes read as binary integers. -/
noncomputable def ϱ : ℝ := ∑' k : ℕ, (bit k : ℝ) / 2 ^ (k + 1)

/-- The challenge's constant is the library's `A362583.ϱ`: the two are
definitionally equal because the `oddPrime`, `bit`, `ϱ` definitions above are
byte-identical copies of the library's. -/
theorem ϱ_eq : ϱ = A362583.ϱ := rfl

/-- **Solution to the comparator challenge**: the challenge statement
`Irrational Challenge.ϱ`, proved by transporting the library's
`A362583.irrational_ϱ` across `ϱ_eq`. -/
theorem irrational_ϱ : Irrational ϱ := ϱ_eq ▸ A362583.irrational_ϱ

end Challenge
