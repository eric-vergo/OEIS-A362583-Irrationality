# A362583 Irrationality

A **complete, `sorry`-free** Lean 4 formalization that the
[OEIS A362583](https://oeis.org/A362583) constant (x ≈ 0.7004…, whose k-th binary
digit is 1 iff the k-th odd prime is ≡ 3 mod 4) is irrational. Pinned to Lean
`v4.31.0` and Mathlib `v4.31.0`.

Main results (`#print axioms` = `{propext, Classical.choice, Quot.sound}` for both):

- `A362583.irrational_x : Irrational x` — the constant is irrational
  (`A362583/Main.lean`).
- `A362583.raceSum_not_linear` — the mod-4 Chebyshev race sum is never
  `c·π(N) + O(1)` for any real `c` (`A362583/CaseZero.lean`; the substantive
  analytic engine — needs only the continued `L(s, χ₄)`, `L(1, χ₄) ≠ 0`, the
  Euler product, `Σ 1/p = ∞`, and the identity theorem; no PNT, no zero-free
  regions).

Verify with `bash scripts/check.sh --strict` (build + hygiene greps + axiom
assertion). Statements are frozen at `git tag statement-lock`.

License: **CC0 1.0 Universal** (public domain — see `LICENSE`). Project metadata
per the [formalization.yaml](https://github.com/mathlib-initiative/formalization.yaml)
standard lives in `formalization.yaml`. A browsable blueprint site (per-node pages,
dependency graph, dashboard) is generated from this repo by the `verso-a362583`
consumer in the local `verso-workspace`.

Layout: `A362583/` — the
formalization library; `Audit/` — Mathlib dependency MWEs; `PROOF.md` — the informal
proof (source of truth; every lemma cites a §2 label); `DEPENDENCIES.md` — the Mathlib
audit table; `SORRIES.md` — tracked sorries; `scripts/check.sh` — build + hygiene gate.
The full project specification lives in the `prime_race` repo
(`a362583-lean-irrationality-spec.md`).
