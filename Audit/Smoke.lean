import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Nth
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Algebra.BigOperators.Module

/-!
# Smoke test (Phase 0a)

Imports every Mathlib module named in the §4 dependency audit and checks two
anchor declarations resolve. If this file compiles Mathlib from source instead
of using cached oleans, the cache is broken — stop and re-diagnose.
-/

#check @DirichletCharacter.LFunction
#check @ZMod.χ₄
