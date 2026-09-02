# A362583 Irrationality

A complete Lean 4 formalization that the
[OEIS A362583](https://oeis.org/A362583) constant is irrational. Pinned to Lean
and Mathlib `v4.33.1`.

*Rokicki's constant* `ϱ` is the sum of the series

```
ϱ = Σ_{k ≥ 0} bₖ · 2^{-(k+1)},   bₖ = 1  ⟺  the k-th odd prime is ≡ 3 (mod 4).
```

Since each `bₖ ∈ {0, 1}`, this is exactly the place-value reading of the binary numeral
`0.b₀b₁b₂…₂`, and these are genuinely *the* binary digits of `ϱ` (infinitely many are `0`,
by Dirichlet at modulus 4, so the digit string is not eventually all `1`s). In decimal,
`ϱ ≈ 0.7004001…`. Reading successive digit prefixes as binary integers recovers the OEIS
integer sequence A362583, which is why we call `ϱ` the A362583 constant.

## What is proved

The deliverable is one theorem:

- **`A362583.irrational_ϱ : Irrational ϱ`** (`A362583/Main.lean`) — the constant is
  irrational.

Its analytic core is an internal milestone, **`A362583.raceSum_not_linear`**
(`A362583/CaseZero.lean`): the mod-4 Chebyshev prime race sum
`S(N) = Σ_{p ≤ N} χ₄(p)` is never linear in the prime count — there are no real
`c, C` with `|S(N) − c·π(N)| ≤ C` for all `N`. It is fully proved and is what
`irrational_ϱ` ultimately rests on, but it is a lemma on the way to the headline
result, not a separately advertised claim; the comparator (below) certifies only
`irrational_ϱ`.

The argument is elementary at the boundary and analytic in the middle. If `ϱ` were
rational its binary digits would be eventually periodic (Dirichlet's theorem on primes in
residue classes, plus a pigeonhole on binary tails), which would force the race sum
`S(N)` to be linear in `π(N)`. The analytic core refutes that using only the analytically
continued Dirichlet L-function `L(s, χ₄)`, its nonvanishing at `s = 1`, the exponential
form of the Euler product, the divergence of `Σ 1/p`, and the identity theorem — no prime
number theorem, no zero-free regions, no quantitative oscillation results.

## Repository layout

| Path | Contents |
|------|----------|
| `A362583/` | The formalization library. `Defs.lean` (the four elementary definitions), `Pins.lean` (sanity checks), `DigitLayer.lean` (the digit layer: infinitely many bits of each value, and eventual periodicity of a rational's digits), `RaceCount.lean` (the race bookkeeping: periodic bits make the race linear), `Character.lean` (the mod-4 Dirichlet character `χ` and the Euler-product layers built from it), `Divergence.lean` (the sole use of the divergence of `Σ 1/p`, isolated as two blow-up statements), `Layers.lean` / `EulerLog.lean` / `BoundedHolo.lean` / `CaseNonzero.lean` / `CaseZero.lean` (the analytic core: the race is never linear), `Main.lean` (final assembly). |
| `A362583.lean` | Library root; imports every module. |
| `comparator/` | Independent-verification bundle for the [comparator](https://github.com/leanprover/comparator) (see below): `Challenge.lean` (the `sorry`d restatement of the main theorem), `Solution.lean` (its proof, derived from `A362583`), `SolutionProbe.lean` (a CI-only sandbox fixture — see the warning below), and `comparator.json` / `comparator-probe.json` / `comparator-status.json` (their configuration and the recorded result). |
| `formalization.yaml` | Project metadata in the [formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) standard. |
| `scripts/` | `check_shared_definitions.sh` — the one check only this repository can state (below). |
| `.github/workflows/` | Two thin callers of the shared pipeline (below). |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | Build configuration. |
| `LICENSE` | Apache License 2.0. |

## Building

With [`elan`](https://github.com/leanprover/elan) installed, the toolchain is picked up
from `lean-toolchain`. Fetch Mathlib's prebuilt artifacts and build:

```bash
lake exe cache get   # download Mathlib oleans (optional but much faster)
lake build           # builds the A362583 library
```

`Challenge`, `Solution` and `SolutionProbe` are declared in `lakefile.toml` but are
deliberately not default targets: their first elaboration belongs inside the comparator's
sandbox, in the CI job that holds no write token.

## Verification status

Everything this project claims to have machine-checked is recorded on the published site
rather than restated here. The site's *Statement comparator* page
(<https://eric-vergo.github.io/OEIS-A362583-Irrationality/comparator/>) says whether, and
when, an independent comparator run certified the theorem — against which separately stated
challenge, under which permitted axioms and checkers — and how to reproduce that run. Its
*Trust model* page (<https://eric-vergo.github.io/OEIS-A362583-Irrationality/Trust-model/>)
says what the site build itself checked, including the kernel axiom audit over the
declarations it presents, and what no tool checks. If this README and the site ever disagree,
the site is the record. The one step no tool performs is reading the formal statement and
deciding that it says what you take it to say; the comparator page shows that statement
verbatim so you can.

## Independent verification

`comparator/Challenge.lean` restates the main theorem (and the three definitions it
mentions) from scratch, importing nothing from the `A362583` library, with proof
`sorry`. This `sorry` is intentional: the file is the input to the
[comparator](https://github.com/leanprover/comparator). Its companion
`comparator/Solution.lean` re-states the same definitions and proves the challenge
theorem by deriving it from the `A362583` library. The comparator elaborates the two
modules in separate environments and certifies, kernel-checked, that the solution proves
this exact statement using only the permitted axioms named in `comparator/comparator.json`.
It requires Linux and is run in CI; `comparator/comparator-status.json` records the result,
and the site's comparator page is generated from that file.

Because the challenge is what the certified claim actually says, its definitions must not
drift from the library's. `scripts/check_shared_definitions.sh` asserts that `oddPrime`,
`bit` and `ϱ` are byte-identical across `A362583/Defs.lean`, `Challenge.lean`,
`Solution.lean` and `SolutionProbe.lean`; it runs in CI and from the repository root.

The commands to reproduce a recorded run — pinned to the comparator, sandbox and
second-kernel revisions that run actually used — are generated on the comparator page from
`comparator/comparator-status.json`, so they name those revisions rather than whatever this
file last said.

⚠️ `comparator/SolutionProbe.lean` is the sandbox regression fixture: elaborating it writes
canary files, which is exactly what CI asks Landlock to refuse. Do not open it in an
elaborating editor outside a sandbox.

## Continuous integration

`.github/workflows/ci.yml` and `deploy.yml` are ~50-line callers of the shared blueprint
pipeline in [eric-vergo/Showcase](https://github.com/eric-vergo/Showcase), pinned by commit
SHA — the same commit `site/lakefile.lean` resolves for `require VersoBlueprint`. The
pipeline's contract, its per-job permissions and its gates are documented in `ci/README.md`
there, and its scripts (the evidence-record validator, the trust-provenance gate, the
source-link and off-origin gates, the release packager) live in `ci/scripts/`.

Its shape: a trusted build job with no write token; a comparator job with no write token, no
OIDC and no secrets, where `Challenge` and `Solution` are elaborated for the first time inside
a Landlock sandbox and replayed by a second, independent kernel; a publish job that validates
that run's evidence record and commits the status artifact back; site build, gates and
packaging; and a release. Pages then serves the release asset a committed pin names, after
`deploy.yml` has checked the asset's digest against that pin. Commits the pipeline makes are
authored by `github-actions[bot]` and carry a `Generated-By: showcase-ci <commit>` trailer
naming the CI code that made them.

## Blueprint site

A browsable blueprint — per-node pages, a dependency graph, and a dashboard, all
generated from this repository — is published at
<https://eric-vergo.github.io/OEIS-A362583-Irrationality/>.

## License

Apache License 2.0 — see `LICENSE`. The OEIS entry it builds on
is © the OEIS Foundation (CC BY-NC 4.0).
