# SORRIES.md — tracked sorries

Every `sorry` in the codebase gets a row here (spec §9).

| File | Decl | §2 label | Blocker | Plan |
|---|---|---|---|---|
| `A362583/Statements.lean` | `irrational_x` | §2.2 / §2.7 assembly | needs Steps A–D (all proved) | Phase 5: chain `eventuallyPeriodic_of_not_irrational` → `raceSum_linear_of_eventuallyPeriodic` → `raceSum_not_linear`, close by contradiction |
Resolved: Steps A + B (`bits_infinite_ones`, `bits_infinite_zeros`,
`eventuallyPeriodic_of_not_irrational`) proved sorry-free in
`A362583/DigitLayer.lean` (Phase 2, 2026-07-03). Step C
(`raceSum_linear_of_eventuallyPeriodic`) proved sorry-free in
`A362583/RaceCount.lean` (Phase 3, 2026-07-03).
