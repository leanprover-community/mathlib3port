/-
Copyright (c) 2014 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import Mathbin.Data.Nat.Cast
import Mathbin.Data.Fintype.Basic
import Mathbin.Tactic.Wlog

/-!
# Characteristic zero

A ring `R` is called of characteristic zero if every natural number `n` is non-zero when considered
as an element of `R`. Since this definition doesn't mention the multiplicative structure of `R`
except for the existence of `1` in this file characteristic zero is defined for additive monoids
with `1`.

## Main definition

`char_zero` is the typeclass of an additive monoid with one such that the natural homomorphism
from the natural numbers into it is injective.

## Main statements

* A linearly ordered semiring has characteristic zero.
* Characteristic zero implies that the additive monoid is infinite.

## TODO

* Once order of a group is defined for infinite additive monoids redefine or at least connect to
  order of `1` in the additive monoid with one.
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
class CharZero (R : Type _) [AddMonoidₓ R] [One R] : Prop where
  cast_injective : Function.Injective (coe : ℕ → R)

theorem char_zero_of_inj_zero {R : Type _} [AddLeftCancelMonoid R] [One R] (H : ∀ n : ℕ, (n : R) = 0 → n = 0) :
    CharZero R :=
  ⟨fun m n => by
    intro h
    wlog hle : m ≤ n
    rcases Nat.Le.dest hle with ⟨k, rfl⟩
    rw [Nat.cast_addₓ, eq_comm, add_right_eq_selfₓ] at h
    rw [H k h, add_zeroₓ]⟩

/-- Note this is not an instance as `char_zero` implies `nontrivial`,
and this would risk forming a loop. -/
theorem OrderedSemiring.to_char_zero {R : Type _} [OrderedSemiring R] [Nontrivial R] : CharZero R :=
  ⟨Nat.strict_mono_cast.Injective⟩

-- see Note [lower instance priority]
instance (priority := 100) LinearOrderedSemiring.to_char_zero {R : Type _} [LinearOrderedSemiring R] : CharZero R :=
  OrderedSemiring.to_char_zero

namespace Nat

variable {R : Type _} [AddMonoidₓ R] [One R] [CharZero R]

theorem cast_injective : Function.Injective (coe : ℕ → R) :=
  CharZero.cast_injective

/-- `nat.cast` as an embedding into monoids of characteristic `0`. -/
@[simps]
def castEmbedding : ℕ ↪ R :=
  ⟨coe, cast_injective⟩

@[simp, norm_cast]
theorem cast_inj {m n : ℕ} : (m : R) = n ↔ m = n :=
  cast_injective.eq_iff

@[simp, norm_cast]
theorem cast_eq_zero {n : ℕ} : (n : R) = 0 ↔ n = 0 := by
  rw [← cast_zero, cast_inj]

@[simp, norm_cast]
theorem cast_eq_one {n : ℕ} : (n : R) = 1 ↔ n = 1 := by
  rw [← cast_one, cast_inj]

@[simp]
theorem cast_pow_eq_one {R : Type _} [Semiringₓ R] [CharZero R] (q : ℕ) (n : ℕ) (hn : n ≠ 0) :
    (q : R) ^ n = 1 ↔ q = 1 := by
  rw [← cast_pow, cast_eq_one]
  exact pow_eq_one_iff hn

@[norm_cast]
theorem cast_ne_zero {n : ℕ} : (n : R) ≠ 0 ↔ n ≠ 0 :=
  cast_eq_zero.Not

@[norm_cast]
theorem cast_ne_one {n : ℕ} : (n : R) ≠ 1 ↔ n ≠ 1 :=
  cast_eq_one.Not

theorem cast_add_one_ne_zero (n : ℕ) : (n + 1 : R) ≠ 0 := by
  exact_mod_cast n.succ_ne_zero

@[simp, norm_cast]
theorem cast_dvd_char_zero {k : Type _} [Field k] [CharZero k] {m n : ℕ} (n_dvd : n ∣ m) : ((m / n : ℕ) : k) = m / n :=
  by
  by_cases' hn : n = 0
  · subst hn
    simp
    
  · exact cast_dvd n_dvd (cast_ne_zero.mpr hn)
    

end Nat

section

variable (M : Type _) [AddMonoidₓ M] [One M] [CharZero M]

-- see Note [lower instance priority]
instance (priority := 100) CharZero.infinite : Infinite M :=
  Infinite.of_injective coe Nat.cast_injective

variable {M}

@[field_simps]
theorem two_ne_zero' : (2 : M) ≠ 0 := by
  have : ((2 : ℕ) : M) ≠ 0 :=
    Nat.cast_ne_zero.2
      (by
        decide)
  rwa [Nat.cast_two] at this

end

section

variable {R : Type _} [NonAssocSemiringₓ R] [NoZeroDivisors R] [CharZero R]

@[simp]
theorem add_self_eq_zero {a : R} : a + a = 0 ↔ a = 0 := by
  simp only [(two_mul a).symm, mul_eq_zero, two_ne_zero', false_orₓ]

@[simp]
theorem bit0_eq_zero {a : R} : bit0 a = 0 ↔ a = 0 :=
  add_self_eq_zero

@[simp]
theorem zero_eq_bit0 {a : R} : 0 = bit0 a ↔ a = 0 := by
  rw [eq_comm]
  exact bit0_eq_zero

end

section

variable {R : Type _} [NonAssocRing R] [NoZeroDivisors R] [CharZero R]

theorem neg_eq_self_iff {a : R} : -a = a ↔ a = 0 :=
  neg_eq_iff_add_eq_zero.trans add_self_eq_zero

theorem eq_neg_self_iff {a : R} : a = -a ↔ a = 0 :=
  eq_neg_iff_add_eq_zero.trans add_self_eq_zero

theorem nat_mul_inj {n : ℕ} {a b : R} (h : (n : R) * a = (n : R) * b) : n = 0 ∨ a = b := by
  rw [← sub_eq_zero, ← mul_sub, mul_eq_zero, sub_eq_zero] at h
  exact_mod_cast h

theorem nat_mul_inj' {n : ℕ} {a b : R} (h : (n : R) * a = (n : R) * b) (w : n ≠ 0) : a = b := by
  simpa [w] using nat_mul_inj h

theorem bit0_injective : Function.Injective (bit0 : R → R) := fun a b h => by
  dsimp' [bit0]  at h
  simp only [(two_mul a).symm, (two_mul b).symm] at h
  refine' nat_mul_inj' _ two_ne_zero
  exact_mod_cast h

theorem bit1_injective : Function.Injective (bit1 : R → R) := fun a b h => by
  simp only [bit1, add_left_injₓ] at h
  exact bit0_injective h

@[simp]
theorem bit0_eq_bit0 {a b : R} : bit0 a = bit0 b ↔ a = b :=
  bit0_injective.eq_iff

@[simp]
theorem bit1_eq_bit1 {a b : R} : bit1 a = bit1 b ↔ a = b :=
  bit1_injective.eq_iff

@[simp]
theorem bit1_eq_one {a : R} : bit1 a = 1 ↔ a = 0 := by
  rw
    [show (1 : R) = bit1 0 by
      simp ,
    bit1_eq_bit1]

@[simp]
theorem one_eq_bit1 {a : R} : 1 = bit1 a ↔ a = 0 := by
  rw [eq_comm]
  exact bit1_eq_one

end

section

variable {R : Type _} [DivisionRing R] [CharZero R]

@[simp]
theorem half_add_self (a : R) : (a + a) / 2 = a := by
  rw [← mul_two, mul_div_cancel a two_ne_zero']

@[simp]
theorem add_halves' (a : R) : a / 2 + a / 2 = a := by
  rw [← add_div, half_add_self]

theorem sub_half (a : R) : a - a / 2 = a / 2 := by
  rw [sub_eq_iff_eq_add, add_halves']

theorem half_sub (a : R) : a / 2 - a = -(a / 2) := by
  rw [← neg_sub, sub_half]

end

namespace WithTop

instance {R : Type _} [AddMonoidₓ R] [One R] [CharZero R] : CharZero (WithTop R) where
  cast_injective := fun m n h => by
    rwa [← coe_nat, ← coe_nat n, coe_eq_coe, Nat.cast_inj] at h

end WithTop

section RingHom

variable {R S : Type _} [NonAssocSemiringₓ R] [NonAssocSemiringₓ S]

theorem RingHom.char_zero (ϕ : R →+* S) [hS : CharZero S] : CharZero R :=
  ⟨fun a b h =>
    CharZero.cast_injective
      (by
        rw [← map_nat_cast ϕ, ← map_nat_cast ϕ, h])⟩

theorem RingHom.char_zero_iff {ϕ : R →+* S} (hϕ : Function.Injective ϕ) : CharZero R ↔ CharZero S :=
  ⟨fun hR =>
    ⟨fun a b h => by
      rwa [← @Nat.cast_inj R _ _ hR, ← hϕ.eq_iff, map_nat_cast ϕ, map_nat_cast ϕ]⟩,
    fun hS => ϕ.char_zero⟩

end RingHom

