/-
Copyright (c) 2026 Eric Vergo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
import A362583.Character

/-!
# Divergence transfer: the sole use of the divergence of `Σ 1/p`

The prime input of the whole argument, isolated: from the divergence of `Σ 1/p`
(`Nat.Primes.not_summable_one_div`) two blow-up statements are transferred to the
prime power sums used downstream.

* `exists_one_lt_tsum_primes_rpow_gt` — `P(s) = Σ_p p^(-s)` blows up as `s ↓ 1`.
* `exists_layerBReal_gt` — `layerBReal` blows up as `s ↓ 1/2`.

Both go through unbounded finite subsums of a nonnegative non-summable family plus a small
continuity padding (`exists_right_of_sum_rpow_gt`) that pushes a finite bound slightly to the
right, where the corresponding `tsum` converges.
-/

namespace A362583

/-- A nonneg non-summable family has unbounded finite subsums. -/
private lemma exists_finset_gt_of_not_summable {f : Nat.Primes → ℝ} (h0 : ∀ p, 0 ≤ f p)
    (hns : ¬ Summable f) (M : ℝ) : ∃ F : Finset Nat.Primes, M < ∑ p ∈ F, f p := by
  by_contra hcon
  exact hns (summable_of_sum_le (Pi.le_def.mpr h0)
    (fun F ↦ not_lt.mp fun hF ↦ hcon ⟨F, hF⟩))

/-- `Σ 1/p` over odd primes is still non-summable (drop the `p = 2` term). -/
private lemma not_summable_one_div_odd :
    ¬ Summable (fun p : Nat.Primes ↦ if (p : ℕ) = 2 then 0 else 1 / ((p : ℕ) : ℝ)) := by
  intro hg
  have htwo : Summable (fun p : Nat.Primes ↦ if (p : ℕ) = 2 then 1 / ((p : ℕ) : ℝ) else 0) := by
    refine summable_of_ne_finset_zero (s := {(⟨2, Nat.prime_two⟩ : Nat.Primes)}) ?_
    intro p hp
    rw [if_neg]
    intro hp2
    exact hp (Finset.mem_singleton.mpr (Subtype.ext hp2))
  have h1 : Summable (fun p : Nat.Primes ↦ 1 / ((p : ℕ) : ℝ)) := by
    refine (hg.add htwo).congr fun p ↦ ?_
    by_cases hp : (p : ℕ) = 2 <;> simp [hp]
  exact Nat.Primes.not_summable_one_div h1

/-- Finite sets of *odd* primes with `Σ 1/p > M` exist for every `M` (feeds the
`layerBReal` blow-up; `Σ_{p odd} 1/p = Σ_p 1/p − 1/2`). -/
private lemma exists_odd_finset_one_div_gt (M : ℝ) :
    ∃ F : Finset Nat.Primes, (∀ p ∈ F, (p : ℕ) ≠ 2) ∧ M < ∑ p ∈ F, 1 / ((p : ℕ) : ℝ) := by
  obtain ⟨F, hF⟩ := exists_finset_gt_of_not_summable
    (fun p ↦ by
      rcases eq_or_ne (p : ℕ) 2 with h | h
      · simp [h]
      · simp only [if_neg h]
        positivity)
    not_summable_one_div_odd M
  refine ⟨F.filter (fun p : Nat.Primes ↦ ¬ (p : ℕ) = 2),
    fun p hp ↦ (Finset.mem_filter.mp hp).2, ?_⟩
  have heq : ∑ p ∈ F.filter (fun p : Nat.Primes ↦ ¬ (p : ℕ) = 2), 1 / ((p : ℕ) : ℝ)
      = ∑ p ∈ F, if (p : ℕ) = 2 then 0 else 1 / ((p : ℕ) : ℝ) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun p _ ↦ ?_
    rcases eq_or_ne (p : ℕ) 2 with hp | hp
    · rw [if_neg (not_not_intro hp), if_pos hp]
    · rw [if_pos hp, if_neg hp]
  rw [heq]
  exact hF

/-- Continuity padding: a finite rpow sum exceeding `M` at `u₀` still exceeds `M`
slightly to the right of `u₀`. -/
private lemma exists_right_of_sum_rpow_gt {F : Finset Nat.Primes} {a u₀ M : ℝ}
    (hM : M < ∑ p ∈ F, ((p : ℕ) : ℝ) ^ (-(a * u₀))) {η : ℝ} (hη : 0 < η) :
    ∃ u : ℝ, u₀ < u ∧ u < u₀ + η ∧ M < ∑ p ∈ F, ((p : ℕ) : ℝ) ^ (-(a * u)) := by
  have hcont : Continuous (fun u : ℝ ↦ ∑ p ∈ F, ((p : ℕ) : ℝ) ^ (-(a * u))) := by
    refine continuous_finsetSum F fun p _ ↦ ?_
    have hrw : (fun u : ℝ ↦ ((p : ℕ) : ℝ) ^ (-(a * u)))
        = fun u ↦ Real.exp (Real.log ((p : ℕ) : ℝ) * (-(a * u))) := by
      funext u
      rw [Real.rpow_def_of_pos (by exact_mod_cast p.prop.pos)]
    rw [hrw]
    fun_prop
  have hopen : IsOpen {u : ℝ | M < ∑ p ∈ F, ((p : ℕ) : ℝ) ^ (-(a * u))} :=
    isOpen_lt continuous_const hcont
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen u₀ hM
  have hmin : 0 < min ε η := lt_min hε hη
  refine ⟨u₀ + min ε η / 2, by linarith, by linarith [min_le_right ε η], ?_⟩
  have hmem : u₀ + min ε η / 2 ∈ Metric.ball u₀ ε := by
    rw [Metric.mem_ball, Real.dist_eq, show u₀ + min ε η / 2 - u₀ = min ε η / 2 by ring,
      abs_of_pos (by linarith)]
    linarith [min_le_left ε η]
  exact hball hmem

/-- **Divergence transfer at `s ↓ 1`**: for every `M` and `η > 0` there is a
real `σ ∈ (1, 1+η)` with `P(σ) = Σ_p p^(-σ) > M`.  Only prime input: the
divergence of `Σ 1/p`. -/
theorem exists_one_lt_tsum_primes_rpow_gt (M : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ σ : ℝ, 1 < σ ∧ σ < 1 + η ∧ M < ∑' p : Nat.Primes, ((p : ℕ) : ℝ) ^ (-σ) := by
  obtain ⟨F, hF⟩ := exists_finset_gt_of_not_summable (fun p ↦ by positivity)
    Nat.Primes.not_summable_one_div M
  have hF1 : M < ∑ p ∈ F, ((p : ℕ) : ℝ) ^ (-(1 * (1 : ℝ))) := by
    refine hF.trans_le (le_of_eq (Finset.sum_congr rfl fun p _ ↦ ?_))
    rw [show -(1 * (1 : ℝ)) = -1 by norm_num, Real.rpow_neg_one, one_div]
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_right_of_sum_rpow_gt hF1 hη
  have hsum : Summable (fun p : Nat.Primes ↦ ((p : ℕ) : ℝ) ^ (-u)) :=
    Nat.Primes.summable_rpow.mpr (by linarith)
  refine ⟨u, hu1, hu2, lt_of_lt_of_le ?_ (hsum.sum_le_tsum F fun p _ ↦ by positivity)⟩
  refine lt_of_lt_of_le hu3 (le_of_eq (Finset.sum_congr rfl fun p _ ↦ ?_))
  rw [one_mul]

/-- Summability of the real `layerB` integrand for `σ > 1/2`. -/
lemma summable_layerBReal_term {σ : ℝ} (hσ : 1 / 2 < σ) :
    Summable (fun p : Nat.Primes ↦ if (p : ℕ) = 2 then 0 else ((p : ℕ) : ℝ) ^ (-(2 * σ))) := by
  refine Summable.of_nonneg_of_le (fun p ↦ ?_) (fun p ↦ ?_)
    (Nat.Primes.summable_rpow.mpr (by linarith : -(2 * σ) < -1))
  · rcases eq_or_ne (p : ℕ) 2 with h | h
    · simp [h]
    · simp only [if_neg h]
      positivity
  · rcases eq_or_ne (p : ℕ) 2 with h | h
    · simp only [if_pos h]
      positivity
    · simp [h]

/-- **Divergence transfer at `s ↓ 1/2` (`layerBReal` blow-up)**: for every `M` and
`η > 0` there is a real `σ ∈ (1/2, 1/2+η)` with `layerBReal σ > M`.  Only prime
input: the divergence of `Σ 1/p`. -/
theorem exists_layerBReal_gt (M : ℝ) {η : ℝ} (hη : 0 < η) :
    ∃ σ : ℝ, 1 / 2 < σ ∧ σ < 1 / 2 + η ∧ M < layerBReal σ := by
  obtain ⟨F, hFodd, hF⟩ := exists_odd_finset_one_div_gt (2 * M)
  have hF1 : 2 * M < ∑ p ∈ F, ((p : ℕ) : ℝ) ^ (-(2 * (1 / 2 : ℝ))) := by
    refine hF.trans_le (le_of_eq (Finset.sum_congr rfl fun p _ ↦ ?_))
    rw [show -(2 * (1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one, one_div]
  obtain ⟨u, hu1, hu2, hu3⟩ := exists_right_of_sum_rpow_gt hF1 hη
  have hsum := summable_layerBReal_term (σ := u) hu1
  have hle : ∑ p ∈ F, ((p : ℕ) : ℝ) ^ (-(2 * u))
      ≤ ∑' p : Nat.Primes, if (p : ℕ) = 2 then 0 else ((p : ℕ) : ℝ) ^ (-(2 * u)) := by
    have heq : ∑ p ∈ F, ((p : ℕ) : ℝ) ^ (-(2 * u))
        = ∑ p ∈ F, if (p : ℕ) = 2 then 0 else ((p : ℕ) : ℝ) ^ (-(2 * u)) :=
      Finset.sum_congr rfl fun p hp ↦ (if_neg (hFodd p hp)).symm
    rw [heq]
    exact hsum.sum_le_tsum F fun p _ ↦ by
      rcases eq_or_ne (p : ℕ) 2 with h | h
      · simp [h]
      · simp only [if_neg h]
        positivity
  refine ⟨u, hu1, hu2, ?_⟩
  unfold layerBReal
  linarith

end A362583
