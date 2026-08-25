# A362583 Irrationality

A complete, `sorry`-free Lean 4 formalization that the
[OEIS A362583](https://oeis.org/A362583) constant is irrational. Pinned to Lean
and Mathlib `v4.32.0`.

The *prime race constant* `ϱ` is the sum of the series

```
ϱ = Σ_{k ≥ 0} bₖ · 2^{-(k+1)},   bₖ = 1  ⟺  the k-th odd prime is ≡ 3 (mod 4).
```

Since each `bₖ ∈ {0, 1}`, this is exactly the place-value reading of the binary numeral
`0.b₀b₁b₂…₂`, and these are genuinely *the* binary digits of `ϱ` (infinitely many are `0`,
by Dirichlet at modulus 4, so the digit string is not eventually all `1`s). In decimal,
`ϱ ≈ 0.7004001…`. Reading successive digit prefixes as binary integers recovers the OEIS
integer sequence A362583, which is why we call `ϱ` the A362583 constant.

## What is proved

The deliverable is one theorem, with axiom footprint
`{propext, Classical.choice, Quot.sound}`:

- **`A362583.irrational_ϱ : Irrational ϱ`** (`A362583/Main.lean`) — the constant is
  irrational.

Its analytic core is an internal milestone, **`A362583.raceSum_not_linear`**
(`A362583/CaseZero.lean`): the mod-4 Chebyshev prime race sum
`S(N) = Σ_{p ≤ N} χ₄(p)` is never linear in the prime count — there are no real
`c, C` with `|S(N) − c·π(N)| ≤ C` for all `N`. It is fully proved (same axiom
footprint) and is what `irrational_ϱ` ultimately rests on, but it is a lemma on the
way to the headline result, not a separately advertised claim; the comparator
(below) certifies only `irrational_ϱ`.

The argument is elementary at the boundary and analytic in the middle. If `ϱ` were
rational its binary digits would be eventually periodic (Steps A–B: Dirichlet's
theorem on primes in residue classes, plus a pigeonhole on binary tails), which would
force the race sum `S(N)` to be linear in `π(N)` (Step C). Step D refutes that using
only the analytically continued Dirichlet L-function `L(s, χ₄)`, its nonvanishing at
`s = 1`, the exponential form of the Euler product, the divergence of `Σ 1/p`, and the
identity theorem — no prime number theorem, no zero-free regions, no quantitative
oscillation results.

## Repository layout

| Path | Contents |
|------|----------|
| `A362583/` | The formalization library. `Defs.lean` (the four elementary definitions), `Pins.lean` (sanity checks), `DigitLayer.lean` (Steps A, B), `RaceCount.lean` (Step C), `Character.lean` (the mod-4 Dirichlet character `χ` and the Euler-product layers built from it), `Divergence.lean` (the sole use of the divergence of `Σ 1/p`, isolated as two blow-up statements), `Layers.lean` / `EulerLog.lean` / `BoundedHolo.lean` / `CaseNonzero.lean` / `CaseZero.lean` (Step D), `Main.lean` (final assembly). |
| `A362583.lean` | Library root; imports every module. |
| `comparator/` | Independent-verification bundle for the [comparator](https://github.com/leanprover/comparator) (see below): `Challenge.lean` (the `sorry`d restatement of the main theorem), `Solution.lean` (its proof, derived from `A362583`), and `comparator.json` / `comparator-status.json` (its configuration and status). |
| `formalization.yaml` | Project metadata in the [formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) standard. |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | Build configuration. |
| `LICENSE` | Apache License 2.0. |

## How to verify

With [`elan`](https://github.com/leanprover/elan) installed, the toolchain is picked up
from `lean-toolchain`. Fetch Mathlib's prebuilt artifacts and build:

```bash
lake exe cache get   # download Mathlib oleans (optional but much faster)
lake build           # builds the A362583, Challenge, and Solution libraries
```

The `A362583` library is `sorry`-free — but a green `lake build` is not by itself the check
for that. The same command also builds `Challenge`, and `comparator/Challenge.lean` carries
exactly one deliberate `sorry`: that file is the comparator's *input*, an independent
restatement of the claim with no proof (see [Independent verification](#independent-verification)
below, and the `Challenge` stanza in `lakefile.toml`, where the sorry warning is documented as
expected). What does check it mechanically is the axiom footprint. Elaborate:

```lean
import A362583.Main

#print axioms A362583.irrational_ϱ
```

This prints exactly

```
'A362583.irrational_ϱ' depends on axioms: [propext, Classical.choice, Quot.sound]
```

— the three standard axioms of Lean's classical logic, and no others. `sorryAx` would appear
in that list if the proof rested on a `sorry`, directly or through any dependency.

CI performs the same check without being asked: the blueprint site build (see below) runs
`collectAxioms` over every declaration it presents and over every declaration named in
`formalization.yaml`, and fails if a closure falls outside those three axioms.

## Independent verification

`comparator/Challenge.lean` restates the main theorem (and the three definitions it
mentions) from scratch, importing nothing from the `A362583` library, with proof
`sorry`. This `sorry` is intentional: the file is the input to the
[comparator](https://github.com/leanprover/comparator). Its companion
`comparator/Solution.lean` re-states the same definitions and proves the challenge
theorem by deriving it from the `A362583` library. The comparator elaborates the two
modules in separate environments and certifies, kernel-checked, that the solution proves
this exact statement using only the permitted axioms. The comparator requires Linux and
is run in CI; `comparator/comparator-status.json` records the result.

To reproduce the check locally (on Linux), check the comparator out as `comparator-tool`
— a sibling of this repository's own `comparator/` folder, so the two never collide — and
run it from the repository root. The commands below are the ones CI runs, at the same
commits; they need a Go toolchain and a Rust toolchain in addition to `elan`.

```bash
# The comparator tool, at the exact commit CI uses (tag v4.33.0).
git clone https://github.com/leanprover/comparator.git comparator-tool
git -C comparator-tool checkout --detach 3927ad383f208ae977c340a91c48ac9b497d2097
# Build it with THIS project's toolchain, as CI does: lean4export has to load the
# project's oleans, which carry a compiler stamp, and the replay then runs on the
# kernel of the release this project pins.
cp lean-toolchain comparator-tool/lean-toolchain
( cd comparator-tool && lake build lean4export comparator )

# The Landlock sandbox and the independent second kernel, at the commits CI uses.
mkdir -p verifier-bin
GOBIN="$PWD/verifier-bin" go install \
  github.com/zouuup/landrun/cmd/landrun@811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
git clone https://github.com/ammkrn/nanoda_lib.git nanoda_lib
git -C nanoda_lib checkout --detach 05055695879dfebb6628a67da88ceca6cd6b0421
cargo build --release --locked --manifest-path nanoda_lib/Cargo.toml
install -m 0755 nanoda_lib/target/release/nanoda_bin verifier-bin/nanoda_bin

export COMPARATOR_LANDRUN="$PWD/verifier-bin/landrun"
export COMPARATOR_NANODA="$PWD/verifier-bin/nanoda_bin"
export COMPARATOR_LEAN4EXPORT="$PWD/comparator-tool/.lake/packages/lean4export/.lake/build/bin/lean4export"
lake env comparator-tool/.lake/build/bin/comparator comparator/comparator.json
```

`tool_sha` in `comparator/comparator-status.json` records that comparator commit and
`tool_ref` the tag naming it; CI asserts on every run both that its own checkout sits at that
commit and that the tag still resolves to it, so the tag moving upstream is a build failure
rather than a silent change of what was certified.

The two verifier binaries are what make the check as strong as CI's, and skipping them
weakens it in ways worth stating. Without `COMPARATOR_LANDRUN` the comparator uses its
bundled `fake-landrun.sh`, a no-op shim: the kernel replay still runs, but unsandboxed.
(Landlock needs Linux ≥ 5.13; CI additionally self-tests, before certifying anything, that a
write outside the allowed paths is genuinely denied.) `COMPARATOR_NANODA` supplies the
independent second kernel that `enable_nanoda` in `comparator.json` asks for — set it, or
turn `enable_nanoda` off and accept a replay checked by Lean's kernel alone.

## Blueprint site

A browsable blueprint — per-node pages, a dependency graph, and a dashboard, all
generated from this repository — is published at
<https://eric-vergo.github.io/OEIS-A362583-Irrationality/>.

## License

Apache License 2.0 — see `LICENSE`. The OEIS entry it builds on
is © the OEIS Foundation (CC BY-NC 4.0).
