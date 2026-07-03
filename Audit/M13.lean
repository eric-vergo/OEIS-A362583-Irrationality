import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed

/-! M13: tsum manipulation for splitting Σ_p Σ_k into k-layers (spec §4) -/

-- Double-sum regrouping (InfiniteSum/Constructions.lean; to_additive names off Multipliable.*;
-- needs Summable on the TOTAL (sigma/prod) type + complete T0 uniform add group, e.g. ℝ, ℂ):
#check @Summable.tsum_prod   -- (h : Summable f) : ∑' p : β × γ, f p = ∑' b, ∑' c, f (b, c)
#check @Summable.tsum_prod'  -- variant taking per-fiber summability explicitly
#check @Summable.tsum_sigma  -- (ha : Summable f) : ∑' p, f p = ∑' b, ∑' c, f ⟨b, c⟩
#check @Summable.tsum_comm   -- (h : Summable (uncurry f)) : ∑' c, ∑' b, f b c = ∑' b, ∑' c, f b c
#check @Summable.prod_factor -- fiber summability from total summability
#check @Summable.sigma_factor

-- Peeling finitely many terms off ∑' over ℕ (InfiniteSum/NatInt.lean, T2 add group):
#check @Summable.sum_add_tsum_nat_add
-- (k : ℕ) (h : Summable f) : ∑ i ∈ range k, f i + ∑' i, f (i + k) = ∑' i, f i
#check @Summable.tsum_eq_zero_add  -- ∑' b, f b = f 0 + ∑' b, f (b + 1)
#check @summable_nat_add_iff       -- Summable (fun n ↦ f (n + k)) ↔ Summable f

-- Comparison tests:
#check @Summable.of_norm_bounded
-- [CompleteSpace E] {f : ι → E} {g : ι → ℝ} (hg : Summable g) (h : ∀ i, ‖f i‖ ≤ g i)
-- NB: g is implicit in this pin (comes first as `hg`); often needs (g := ...) to guide it.
#check @Summable.of_norm_bounded_eventually_nat
#check @Summable.of_nonneg_of_le   -- (0 ≤ g) → (g ≤ f) → Summable f → Summable g  (ℝ-valued)

-- Geometric sums and tails (Analysis/SpecificLimits/{Basic,Normed}.lean):
#check @tsum_geometric_of_lt_one          -- (0 ≤ r) (r < 1) : ∑' n, r ^ n = (1 - r)⁻¹
#check @tsum_geometric_of_norm_lt_one     -- normed-field version
#check @tsum_geometric_le_of_norm_lt_one  -- ‖∑' n, x ^ n‖ ≤ ‖1‖ - 1 + (1 - ‖x‖)⁻¹

-- THE T(s) MOVE: split ∑' k, f k into f 0 + f 1 + f 2 + (k ≥ 3 tail reindexed by k + 3):
example (f : ℕ → ℝ) (hf : Summable f) :
    ∑' k, f k = f 0 + f 1 + f 2 + ∑' k, f (k + 3) := by
  rw [← hf.sum_add_tsum_nat_add 3, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]

-- regrouping smoke test (ℝ is a complete T0 uniform add group):
example (f : ℕ × ℕ → ℝ) (hf : Summable f) :
    ∑' p : ℕ × ℕ, f p = ∑' n, ∑' k, f (n, k) :=
  hf.tsum_prod
