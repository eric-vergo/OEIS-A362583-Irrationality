# A362583 Irrationality

A complete, `sorry`-free Lean 4 formalization that the
[OEIS A362583](https://oeis.org/A362583) constant is irrational. Pinned to Lean
and Mathlib `v4.31.0`.

The constant is

```
x = 0.b₀b₁b₂…  (binary),   bₖ = 1  ⟺  the k-th odd prime is ≡ 3 (mod 4),
```

so `x ≈ 0.7004001…`.

## What is proved

The deliverable is one theorem, with axiom footprint
`{propext, Classical.choice, Quot.sound}`:

- **`A362583.irrational_x : Irrational x`** (`A362583/Main.lean`) — the constant is
  irrational.

Its analytic core is an internal milestone, **`A362583.raceSum_not_linear`**
(`A362583/CaseZero.lean`): the mod-4 Chebyshev prime race sum
`S(N) = Σ_{p ≤ N} χ₄(p)` is never linear in the prime count — there are no real
`c, C` with `|S(N) − c·π(N)| ≤ C` for all `N`. It is fully proved (same axiom
footprint) and is what `irrational_x` ultimately rests on, but it is a lemma on the
way to the headline result, not a separately advertised claim; the comparator
(below) certifies only `irrational_x`.

The argument is elementary at the boundary and analytic in the middle. If `x` were
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
| `A362583/` | The formalization library. `Defs.lean` (the four elementary definitions), `Pins.lean` (sanity checks), `DigitLayer.lean` (Steps A, B), `RaceCount.lean` (Step C), `Layers.lean` / `EulerLog.lean` / `BoundedHolo.lean` / `CaseNonzero.lean` / `CaseZero.lean` (Step D), `Main.lean` (final assembly). |
| `A362583.lean` | Library root; imports every module. |
| `Challenge/`, `Challenge.lean` | An independent restatement of the main theorem for the comparator (see below). |
| `comparator.json`, `comparator-status.json` | Comparator configuration and status. |
| `formalization.yaml` | Project metadata in the [formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml) standard. |
| `lakefile.toml`, `lean-toolchain`, `lake-manifest.json` | Build configuration. |
| `LICENSE` | Apache License 2.0. |

## How to verify

With [`elan`](https://github.com/leanprover/elan) installed, the toolchain is picked up
from `lean-toolchain`. Fetch Mathlib's prebuilt artifacts and build:

```bash
lake exe cache get   # download Mathlib oleans (optional but much faster)
lake build           # builds the A362583 and Challenge libraries
```

A successful build is `sorry`-free by construction. To check the axiom footprint of the
main result, elaborate:

```lean
import A362583.Main

#print axioms A362583.irrational_x
```

This prints exactly

```
'A362583.irrational_x' depends on axioms: [propext, Classical.choice, Quot.sound]
```

— the three standard axioms of Lean's classical logic, and no others.

## Independent verification

`Challenge/Challenge.lean` restates the main theorem (and the three definitions it
mentions) from scratch, importing nothing from the `A362583` library, with proof
`sorry`. This `sorry` is intentional: the file is the input to the
[comparator](https://github.com/leanprover/comparator), which elaborates the challenge
and the library in separate environments and certifies, kernel-checked, that the library
proves this exact statement using only the permitted axioms. The comparator requires
Linux and is run in CI; `comparator-status.json` records the result.

## Blueprint site

A browsable blueprint — per-node pages, a dependency graph, and a dashboard, all
generated from this repository — is published at
<https://eric-vergo.github.io/OEIS-A362583-Irrationality/>.

## License

Apache License 2.0 — see `LICENSE`. The OEIS entry it builds on
is © the OEIS Foundation (CC BY-NC 4.0).
