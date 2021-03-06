/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Int.Cast.Defs

/-!
# Characteristic zero

A ring `R` is called of characteristic zero if every natural number `n` is non-zero when considered
as an element of `R`. Since this definition doesn't mention the multiplicative structure of `R`
except for the existence of `1` in this file characteristic zero is defined for additive monoids
with `1`.

## Main definition

`char_zero` is the typeclass of an additive monoid with one such that the natural homomorphism
from the natural numbers into it is injective.

## TODO

* Unify with `char_p` (possibly using an out-parameter)
-/


/-- Typeclass for monoids with characteristic zero.
  (This is usually stated on fields but it makes sense for any additive monoid with 1.)

*Warning*: for a semiring `R`, `char_zero R` and `char_p R 0` need not coincide.
* `char_zero R` requires an injection `ℕ ↪ R`;
* `char_p R 0` asks that only `0 : ℕ` maps to `0 : R` under the map `ℕ → R`.

For instance, endowing `{0, 1}` with addition given by `max` (i.e. `1` is absorbing), shows that
`char_zero {0, 1}` does not hold and yet `char_p {0, 1} 0` does.
This example is formalized in `counterexamples/char_p_zero_ne_char_zero`.
 -/
class CharZero (R : Type _) [AddMonoidWithOneₓ R] : Prop where
  cast_injective : Function.Injective (coe : ℕ → R)

theorem char_zero_of_inj_zero {R : Type _} [AddGroupWithOneₓ R] (H : ∀ n : ℕ, (n : R) = 0 → n = 0) : CharZero R :=
  ⟨fun m n h => by
    induction' m with m ih generalizing n
    · rw [H n]
      rw [← h, Nat.cast_zeroₓ]
      
    cases' n with n
    · apply H
      rw [h, Nat.cast_zeroₓ]
      
    simp_rw [Nat.cast_succₓ, add_right_cancel_iffₓ] at h
    rwa [ih]⟩

namespace Nat

variable {R : Type _} [AddMonoidWithOneₓ R] [CharZero R]

theorem cast_injective : Function.Injective (coe : ℕ → R) :=
  CharZero.cast_injective

@[simp, norm_cast]
theorem cast_inj {m n : ℕ} : (m : R) = n ↔ m = n :=
  cast_injective.eq_iff

@[simp, norm_cast]
theorem cast_eq_zero {n : ℕ} : (n : R) = 0 ↔ n = 0 := by
  rw [← cast_zero, cast_inj]

@[norm_cast]
theorem cast_ne_zero {n : ℕ} : (n : R) ≠ 0 ↔ n ≠ 0 :=
  not_congr cast_eq_zero

theorem cast_add_one_ne_zero (n : ℕ) : (n + 1 : R) ≠ 0 := by
  exact_mod_cast n.succ_ne_zero

@[simp, norm_cast]
theorem cast_eq_one {n : ℕ} : (n : R) = 1 ↔ n = 1 := by
  rw [← cast_one, cast_inj]

@[norm_cast]
theorem cast_ne_one {n : ℕ} : (n : R) ≠ 1 ↔ n ≠ 1 :=
  cast_eq_one.Not

end Nat

