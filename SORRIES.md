# SORRIES.md — tracked sorries

Every `sorry` in the codebase gets a row here (spec §9).

| File | Decl | §2 label | Blocker | Plan |
|---|---|---|---|---|
| `A362583/Statements.lean` | `raceSum_not_linear` | §2.6 Step D | Phase 4 (analytic engine) not started | 4a: N1 bounded-sums holomorphy; 4b: D0a/D0b; 4c: D0c/D0d Euler–L wiring (M2–M4); 4d: case c ≠ 0; 4e: case c = 0 (identity theorem M8) |
| `A362583/Statements.lean` | `irrational_x` | §2.2 / §2.7 assembly | needs Steps A–D | Phase 5: chain `eventuallyPeriodic_of_not_irrational` → `raceSum_linear_of_eventuallyPeriodic` → `raceSum_not_linear`, close by contradiction |
| `A362583/Statements.lean` | `bits_infinite_ones` | §2.3 Step A | Phase 2 not started | `Nat.infinite_setOf_prime_and_eq_mod` at q = 4, a = 3 (M6) + ZMod↔% bridge + `Nat.nth` reindexing (M7) |
| `A362583/Statements.lean` | `bits_infinite_zeros` | §2.3 Step A | Phase 2 not started | same as `bits_infinite_ones` with a = 1 |
| `A362583/Statements.lean` | `eventuallyPeriodic_of_not_irrational` | §2.4 Step B | Phase 2 not started | N2 pigeonhole on tails `t_k = fract (2^k x)` (B1–B5); `Int.fract` API (M11), consider `Real.ofDigits` infra (M14 note) |
| `A362583/Statements.lean` | `raceSum_linear_of_eventuallyPeriodic` | §2.5 Step C | Phase 3 not started | N3 bookkeeping: ones-count of periodic tail is `(j/P)·m + O(1)`; translate `k`-th odd prime ↔ primes ≤ N via `Nat.nth`/`Nat.count` Galois connection (M7) |
