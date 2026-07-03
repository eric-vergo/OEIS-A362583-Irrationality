/-
Axiom audit for the two main theorems (spec §7.2).
Expected output: each `#print axioms` lists a subset of
{propext, Classical.choice, Quot.sound} — nothing else (in particular
no `sorryAx`, no `Lean.ofReduceBool`).
-/
import A362583

#print axioms A362583.irrational_x
#print axioms A362583.raceSum_not_linear
