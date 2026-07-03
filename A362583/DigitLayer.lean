/-
Copyright (c) 2026 Eric Vergo. Dedicated to the public domain.
Released under CC0 1.0 Universal as described in the file LICENSE.
Authors: Eric Vergo, Claude Fable 5 (Claude Code)
-/
import A362583.Defs
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.Order.Floor.Ring

/-!
# A362583: the digit layer (spec §2.3 Step A, §2.4 Step B)

* **Step A** (`bits_infinite_ones`, `bits_infinite_zeros`): both residue classes
  mod 4 contain infinitely many primes (Dirichlet, audit M6), hence the bit
  sequence has infinitely many ones and infinitely many zeros.  The transfer
  from primes to bit indices is the injection `p ↦ Nat.count Nat.Prime p - 1`,
  inverted by `oddPrime` via `Nat.nth_count` (audit M7).

* **Step B** (`eventuallyPeriodic_of_not_irrational`): if `x` is rational its
  bit sequence is eventually periodic — the N2 pigeonhole on the binary tails
  `t k = ∑_{j≥0} b_{k+j} 2^{-(j+1)}` (spec §2.4's `t_k`, with `t 0 = x`),
  following B1–B5 verbatim.  No general digit-expansion theory is used.
-/

namespace A362583

/-! ## Step A (spec §2.3): both bit values occur infinitely often -/

/-- §2.3 bookkeeping: `bit k = 1` iff the `k`-th odd prime is `≡ 3 (mod 4)`
(definitional unfolding of `bit`). -/
private lemma bit_eq_one_iff {k : ℕ} : bit k = 1 ↔ oddPrime k % 4 = 3 := by
  unfold bit
  split <;> simp_all

/-- §2.3 bookkeeping: `bit k = 0` iff the `k`-th odd prime is not `≡ 3 (mod 4)`. -/
private lemma bit_eq_zero_iff {k : ℕ} : bit k = 0 ↔ oddPrime k % 4 ≠ 3 := by
  unfold bit
  split <;> simp_all

/-- §2.3: an odd prime `p` is recovered as `oddPrime (Nat.count Nat.Prime p - 1)`;
the count is `≥ 1` because `2 < p` and `2` is prime (audit M7: `Nat.nth_count`). -/
private lemma oddPrime_count {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    oddPrime (Nat.count Nat.Prime p - 1) = p := by
  have h3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h1 : 1 ≤ Nat.count Nat.Prime p :=
    le_trans (by decide : 1 ≤ Nat.count Nat.Prime 3) (Nat.count_monotone _ h3)
  unfold oddPrime
  rw [Nat.sub_add_cancel h1]
  exact Nat.nth_count hp

/-- §2.3 transfer: an infinite set of primes avoiding `2` pulls back to an
infinite set of `oddPrime`-indices along the injection `p ↦ count Prime p - 1`. -/
private lemma infinite_oddPrime_index {S : Set ℕ} (hS : S.Infinite)
    (hSp : ∀ p ∈ S, p.Prime) (hS2 : 2 ∉ S) : {k : ℕ | oddPrime k ∈ S}.Infinite := by
  have key : ∀ p ∈ S, oddPrime (Nat.count Nat.Prime p - 1) = p := by
    intro p hpS
    refine oddPrime_count (hSp p hpS) ?_
    rintro rfl
    exact hS2 hpS
  refine Set.infinite_of_injOn_mapsTo (f := fun p => Nat.count Nat.Prime p - 1) ?_ ?_ hS
  · intro p₁ h₁ p₂ h₂ heq
    have e₁ := key p₁ h₁
    have e₂ := key p₂ h₂
    simp only at heq
    rw [heq, e₂] at e₁
    exact e₁.symm
  · intro p hpS
    show oddPrime (Nat.count Nat.Prime p - 1) ∈ S
    rw [key p hpS]
    exact hpS

/-- §2.3: infinitude of primes `≡ 3 (mod 4)` in `%`-form — Dirichlet
(`Nat.infinite_setOf_prime_and_eq_mod`, audit M6) plus the ZMod↔`%` bridge. -/
private lemma infinite_primes_three_mod_four : {p : ℕ | p.Prime ∧ p % 4 = 3}.Infinite := by
  have h : {p : ℕ | p.Prime ∧ (p : ZMod 4) = 3}.Infinite :=
    Nat.infinite_setOf_prime_and_eq_mod (by decide)
  have hset : {p : ℕ | p.Prime ∧ (p : ZMod 4) = 3} = {p : ℕ | p.Prime ∧ p % 4 = 3} := by
    ext p
    have hbr : (p : ZMod 4) = 3 ↔ p % 4 = 3 := by
      rw [← Nat.cast_ofNat (R := ZMod 4) (n := 3), ZMod.natCast_eq_natCast_iff']
    simp only [Set.mem_setOf_eq, hbr]
  rwa [hset] at h

/-- §2.3: infinitude of primes `≡ 1 (mod 4)` in `%`-form (audit M6). -/
private lemma infinite_primes_one_mod_four : {p : ℕ | p.Prime ∧ p % 4 = 1}.Infinite := by
  have h : {p : ℕ | p.Prime ∧ (p : ZMod 4) = 1}.Infinite :=
    Nat.infinite_setOf_prime_and_eq_mod isUnit_one
  have hset : {p : ℕ | p.Prime ∧ (p : ZMod 4) = 1} = {p : ℕ | p.Prime ∧ p % 4 = 1} := by
    ext p
    have hbr : (p : ZMod 4) = 1 ↔ p % 4 = 1 := by
      rw [← Nat.cast_one (R := ZMod 4), ZMod.natCast_eq_natCast_iff']
    simp only [Set.mem_setOf_eq, hbr]
  rwa [hset] at h

/-- **Step A** (spec §2.3): infinitely many primes are `≡ 3 (mod 4)`, so the bit
sequence contains infinitely many ones. -/
lemma bits_infinite_ones : {k | bit k = 1}.Infinite := by
  have hidx := infinite_oddPrime_index infinite_primes_three_mod_four
    (fun p hp => hp.1) (fun h => absurd h.2 (by decide))
  refine hidx.mono fun k hk => ?_
  exact bit_eq_one_iff.mpr hk.2

/-- **Step A** (spec §2.3): infinitely many primes are `≡ 1 (mod 4)`, so the bit
sequence contains infinitely many zeros. -/
lemma bits_infinite_zeros : {k | bit k = 0}.Infinite := by
  have hidx := infinite_oddPrime_index infinite_primes_one_mod_four
    (fun p hp => hp.1) (fun h => absurd h.2 (by decide))
  refine hidx.mono fun k hk => ?_
  have h1 : oddPrime k % 4 = 1 := hk.2
  exact bit_eq_zero_iff.mpr (by omega)

/-! ## Step B (spec §2.4): rational ⇒ eventually periodic bits

The tail `t k = ∑_{j≥0} b_{k+j} 2^{-(j+1)}` is spec §2.4's `t_k` under the
0-based reindexing of `Defs.lean` (spec bits are 1-based: `b_{k+1} = bit k`),
so `t 0 = x`, the recurrence B2 reads `t k = (bit k + t (k+1))/2`, and B3 reads
`t k = Int.fract (2^k * x)`. -/

/-- §2.4: the binary tail `t k = ∑_{j≥0} b_{k+j} 2^{-(j+1)}` (spec's `t_k`). -/
private noncomputable def t (k : ℕ) : ℝ := ∑' j : ℕ, (bit (k + j) : ℝ) / 2 ^ (j + 1)

private lemma t_def (k : ℕ) : t k = ∑' j : ℕ, (bit (k + j) : ℝ) / 2 ^ (j + 1) := rfl

/-- §2.4 bookkeeping: bits are `≤ 1`. -/
private lemma bit_le_one (k : ℕ) : bit k ≤ 1 := by
  unfold bit
  split <;> omega

/-- §2.4 bookkeeping: bits are `0` or `1`. -/
private lemma bit_zero_or_one (k : ℕ) : bit k = 0 ∨ bit k = 1 := by
  unfold bit
  split <;> omega

/-- §2.4: tail terms are nonnegative. -/
private lemma term_nonneg (k : ℕ) : ∀ j : ℕ, 0 ≤ (bit (k + j) : ℝ) / 2 ^ (j + 1) :=
  fun j => by positivity

/-- §2.4: tail terms are dominated by the geometric series (audit M13 pattern,
as in `Pins.lean`). -/
private lemma term_le_geom (k : ℕ) :
    ∀ j : ℕ, (bit (k + j) : ℝ) / 2 ^ (j + 1) ≤ ((1 : ℝ) / 2) ^ (j + 1) := by
  intro j
  rw [div_pow, one_pow]
  gcongr
  exact_mod_cast bit_le_one (k + j)

/-- §2.4: the comparison geometric series is summable. -/
private lemma summable_geom : Summable (fun j : ℕ => ((1 : ℝ) / 2) ^ (j + 1)) :=
  (summable_nat_add_iff 1).mpr (summable_geometric_of_lt_one (by norm_num) (by norm_num))

/-- §2.4: the comparison geometric series sums to `1`. -/
private lemma tsum_geom : ∑' j : ℕ, ((1 : ℝ) / 2) ^ (j + 1) = 1 := by
  simp only [pow_succ]
  rw [tsum_mul_right, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-- §2.4: each tail is summable (comparison with the geometric series). -/
private lemma summable_t (k : ℕ) : Summable (fun j : ℕ => (bit (k + j) : ℝ) / 2 ^ (j + 1)) :=
  Summable.of_nonneg_of_le (term_nonneg k) (term_le_geom k) summable_geom

/-- **(B1)** (spec §2.4): `0 < t k`, from infinitely many later ones (Step A). -/
private lemma t_pos (k : ℕ) : 0 < t k := by
  obtain ⟨m, hm, hkm⟩ := bits_infinite_ones.exists_gt k
  have hm' : bit m = 1 := hm
  rw [t_def]
  refine (summable_t k).tsum_pos (term_nonneg k) (m - k) ?_
  rw [show k + (m - k) = m from by omega, hm']
  push_cast
  positivity

/-- **(B1)** (spec §2.4): `t k < 1`, from infinitely many later zeros (Step A);
strictness by the `Pins.lean` incantation `Summable.tsum_lt_tsum_of_nonneg`. -/
private lemma t_lt_one (k : ℕ) : t k < 1 := by
  obtain ⟨m, hm, hkm⟩ := bits_infinite_zeros.exists_gt k
  have hm' : bit m = 0 := hm
  have hstrict : (bit (k + (m - k)) : ℝ) / 2 ^ ((m - k) + 1) < ((1 : ℝ) / 2) ^ ((m - k) + 1) := by
    rw [show k + (m - k) = m from by omega, hm']
    simp only [Nat.cast_zero, zero_div]
    positivity
  calc t k < ∑' j : ℕ, ((1 : ℝ) / 2) ^ (j + 1) :=
        Summable.tsum_lt_tsum_of_nonneg (term_nonneg k) (term_le_geom k) hstrict summable_geom
    _ = 1 := tsum_geom

/-- **(B2)** (spec §2.4): the recurrence `t k = (bit k + t (k+1)) / 2`
(spec's `t_k = (b_{k+1} + t_{k+1})/2`); peel `j = 0` off the tsum (audit M13). -/
private lemma t_rec (k : ℕ) : t k = ((bit k : ℝ) + t (k + 1)) / 2 := by
  have h0 : t k = (bit (k + 0) : ℝ) / 2 ^ (0 + 1)
      + ∑' j : ℕ, (bit (k + (j + 1)) : ℝ) / 2 ^ (j + 1 + 1) :=
    (summable_t k).tsum_eq_zero_add
  have h1 : ∑' j : ℕ, (bit (k + (j + 1)) : ℝ) / 2 ^ (j + 1 + 1)
      = ∑' j : ℕ, (bit (k + 1 + j) : ℝ) / 2 ^ (j + 1) / 2 :=
    tsum_congr fun j => by
      rw [show k + (j + 1) = k + 1 + j from by omega]
      ring
  have h2 : ∑' j : ℕ, (bit (k + 1 + j) : ℝ) / 2 ^ (j + 1) / 2 = t (k + 1) / 2 :=
    tsum_div_const
  rw [h0, h1, h2]
  simp only [Nat.add_zero, Nat.zero_add, pow_one]
  ring

/-- **(B2)** (spec §2.4): `t (k+1) = 2·t k - bit k`. -/
private lemma t_succ (k : ℕ) : t (k + 1) = 2 * t k - (bit k : ℝ) := by
  have := t_rec k
  linarith

/-- **(B2)** (spec §2.4): the tail determines the bit — `bit k = 1 ↔ 1/2 < t k`
(uses B1 at `k+1`; in particular `t k ≠ 1/2`). -/
private lemma bit_one_iff_half_lt (k : ℕ) : bit k = 1 ↔ 1 / 2 < t k := by
  have hrec := t_rec k
  have hpos := t_pos (k + 1)
  have hlt1 := t_lt_one (k + 1)
  constructor
  · intro h
    rw [h] at hrec
    norm_num at hrec
    linarith
  · intro h
    rcases bit_zero_or_one k with h0 | h1
    · rw [h0] at hrec
      norm_num at hrec
      linarith
    · exact h1

/-- **(B2)** consequence (spec §2.4): equal tails give equal bits. -/
private lemma bit_eq_of_t_eq {m n : ℕ} (h : t m = t n) : bit m = bit n := by
  have hm := bit_one_iff_half_lt m
  have hn := bit_one_iff_half_lt n
  rw [h] at hm
  by_cases hlt : 1 / 2 < t n
  · rw [hm.mpr hlt, hn.mpr hlt]
  · have h1 : bit m ≠ 1 := fun hh => hlt (hm.mp hh)
    have h2 : bit n ≠ 1 := fun hh => hlt (hn.mp hh)
    rcases bit_zero_or_one m with e | e <;> rcases bit_zero_or_one n with f | f <;> omega

/-- **(B5)** induction (spec §2.4): a tail collision propagates to all later
indices, via B2's determinism. -/
private lemma t_eq_add {m n : ℕ} (h : t m = t n) (i : ℕ) : t (m + i) = t (n + i) := by
  induction i with
  | zero => simpa using h
  | succ i ih =>
    have hb := bit_eq_of_t_eq ih
    show t ((m + i) + 1) = t ((n + i) + 1)
    rw [t_succ, t_succ, ih, hb]

/-- **(B3)** (spec §2.4): `t k = fract (2^k x)` — the binary prefix of `2^k x`
is an integer and the tail lies in `[0,1)` (audit M11: `Int.fract_intCast_add`). -/
private lemma t_eq_fract (k : ℕ) : t k = Int.fract ((2 : ℝ) ^ k * x) := by
  induction k with
  | zero =>
    have h0 : t 0 = x := tsum_congr fun j => by rw [Nat.zero_add]
    rw [pow_zero, one_mul, ← h0, Int.fract_eq_self.mpr ⟨(t_pos 0).le, t_lt_one 0⟩]
  | succ k ih =>
    have hfl : (2 : ℝ) ^ k * x = (⌊(2 : ℝ) ^ k * x⌋ : ℝ) + t k := by
      rw [ih]
      exact (Int.floor_add_fract _).symm
    have hsucc := t_succ k
    have hkey : (2 : ℝ) ^ (k + 1) * x
        = ((2 * ⌊(2 : ℝ) ^ k * x⌋ + (bit k : ℤ) : ℤ) : ℝ) + t (k + 1) := by
      push_cast
      linear_combination 2 * hfl - hsucc
    rw [hkey, Int.fract_intCast_add, Int.fract_eq_self.mpr ⟨(t_pos _).le, t_lt_one _⟩]

/-- **(B4)** (spec §2.4): if `x` is rational then the tails
`t k = fract (2^k · a/b) ∈ {0, 1/b, …, (b-1)/b}` take finitely many values, so
two collide (pigeonhole through `ZMod q.den`; audit M11 for the fract step). -/
private lemma exists_t_collision (h : ¬ Irrational x) : ∃ m n : ℕ, m < n ∧ t m = t n := by
  obtain ⟨q, hq⟩ := exists_rat_of_not_irrational h
  have key : ∀ k : ℕ, t k = ((2 ^ k * q.num % (q.den : ℤ) : ℤ) : ℝ) / ((q.den : ℕ) : ℝ) := by
    intro k
    rw [t_eq_fract, hq, Rat.cast_def]
    rw [show (2 : ℝ) ^ k * ((q.num : ℝ) / ((q.den : ℕ) : ℝ))
        = ((2 ^ k * q.num : ℤ) : ℝ) / ((q.den : ℕ) : ℝ) from by push_cast; ring]
    exact Int.fract_div_intCast_eq_div_intCast_mod
  haveI : NeZero q.den := ⟨q.den_pos.ne'⟩
  obtain ⟨k₁, k₂, hne, heq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => ((2 ^ k * q.num : ℤ) : ZMod q.den))
  have hmod : 2 ^ k₁ * q.num % (q.den : ℤ) = 2 ^ k₂ * q.num % (q.den : ℤ) :=
    (ZMod.intCast_eq_intCast_iff' _ _ _).mp heq
  have hteq : t k₁ = t k₂ := by rw [key k₁, key k₂, hmod]
  rcases lt_or_gt_of_ne (a := k₁) (b := k₂) hne with hlt | hlt
  · exact ⟨k₁, k₂, hlt, hteq⟩
  · exact ⟨k₂, k₁, hlt, hteq.symm⟩

/-- **Step B** (spec §2.4, B1–B5): if `x` is rational, its bit sequence is
eventually periodic — pigeonhole two equal tails `t m = t n` (B4), propagate the
collision by B2's determinism (B5), giving period `P = n - m` from index `m`. -/
lemma eventuallyPeriodic_of_not_irrational :
    ¬ Irrational x → ∃ N P, 0 < P ∧ ∀ k ≥ N, bit (k + P) = bit k := by
  intro h
  obtain ⟨m, n, hmn, ht⟩ := exists_t_collision h
  refine ⟨m, n - m, by omega, fun k hk => ?_⟩
  obtain ⟨i, rfl⟩ : ∃ i, k = m + i := ⟨k - m, by omega⟩
  have hbi : bit (m + i) = bit (n + i) := bit_eq_of_t_eq (t_eq_add ht i)
  rw [show m + i + (n - m) = n + i from by omega, ← hbi]

end A362583
