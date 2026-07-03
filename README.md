# A362583 Irrationality

A Lean 4 formalization that the [OEIS A362583](https://oeis.org/A362583) constant
(x ≈ 0.7004…, whose k-th binary digit is 1 iff the k-th odd prime is ≡ 3 mod 4) is
irrational. Pinned to Lean `v4.31.0` and Mathlib `v4.31.0`. Layout: `A362583/` — the
formalization library; `Audit/` — Mathlib dependency MWEs; `PROOF.md` — the informal
proof (source of truth; every lemma cites a §2 label); `DEPENDENCIES.md` — the Mathlib
audit table; `SORRIES.md` — tracked sorries; `scripts/check.sh` — build + hygiene gate.
The full project specification lives in the `prime_race` repo
(`a362583-lean-irrationality-spec.md`).
