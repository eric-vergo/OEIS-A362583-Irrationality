import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Prime.Nth

/-! M7: Nat.nth / Nat.count / Nat.primeCounting toolkit + sanity pins (spec §4) -/

#check @Nat.count      -- count p n = #{k | k < n ∧ p k}  (STRICT upper bound)
#check @Nat.nth_count  -- (hpn : p n) : nth p (count p n) = n
#check @Nat.count_nth  -- (∀ hf : (setOf p).Finite, n < #hf.toFinset) → count p (nth p n) = n
#check @Nat.count_nth_of_infinite -- ((setOf p).Infinite) → count p (nth p n) = n
#check @Nat.nth_lt_nth -- ((setOf p).Infinite) : nth p k < nth p n ↔ k < n
#check @Nat.count_le_iff_le_nth   -- ((setOf p).Infinite) : count p a ≤ b ↔ a ≤ nth p b
#check @Nat.primeCounting'_nth_eq -- π' (nth Nat.Prime n) = n

-- Sanity pins already exist in Mathlib (Data/Nat/Prime/Nth.lean), simp-tagged:
#check (Nat.nth_prime_zero_eq_two : Nat.nth Nat.Prime 0 = 2)
#check (Nat.nth_prime_one_eq_three : Nat.nth Nat.Prime 1 = 3)
#check (Nat.nth_prime_two_eq_five : Nat.nth Nat.Prime 2 = 5)

-- Hand-rolled route: `Nat.count Nat.Prime <numeral>` reduces definitionally,
-- so `nth_count` alone closes the pin (this is Mathlib's own proof).
example : Nat.nth Nat.Prime 0 = 2 := Nat.nth_count Nat.prime_two
example : Nat.nth Nat.Prime 1 = 3 := Nat.nth_count Nat.prime_three

-- The count facts behind the pins are `decide`-able (kernel-friendly primality):
example : Nat.count Nat.Prime 2 = 0 := by decide
example : Nat.count Nat.Prime 3 = 1 := by decide

-- π(10) = 4: BOTH `rfl` and `decide` work.
example : Nat.primeCounting 10 = 4 := rfl
example : Nat.primeCounting 10 = 4 := by decide

-- `count_nth`'s finiteness hypothesis is vacuous for an infinite predicate;
-- discharge with `absurd`:
example : Nat.count Nat.Prime (Nat.nth Nat.Prime 5) = 5 :=
  Nat.count_nth fun hf => absurd hf Nat.infinite_setOf_prime
