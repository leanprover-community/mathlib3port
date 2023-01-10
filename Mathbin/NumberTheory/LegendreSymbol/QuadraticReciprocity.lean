/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Michael Stoll

! This file was ported from Lean 3 source module number_theory.legendre_symbol.quadratic_reciprocity
! leanprover-community/mathlib commit 7b78d1776212a91ecc94cf601f83bdcc46b04213
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.NumberTheory.LegendreSymbol.QuadraticChar

/-!
# Legendre symbol and quadratic reciprocity.

This file contains results about quadratic residues modulo a prime number.

We define the Legendre symbol $\Bigl(\frac{a}{p}\Bigr)$ as `legendre_sym p a`.
Note the order of arguments! The advantage of this form is that then `legendre_sym p`
is a multiplicative map.

The Legendre symbol is used to define the Jacobi symbol, `jacobi_sym a b`, for integers `a`
and (odd) natural numbers `b`, which extends the Legendre symbol.

## Main results

We prove the law of quadratic reciprocity, see `legendre_sym.quadratic_reciprocity` and
`legendre_sym.quadratic_reciprocity'`, as well as the
interpretations in terms of existence of square roots depending on the congruence mod 4,
`zmod.exists_sq_eq_prime_iff_of_mod_four_eq_one`, and
`zmod.exists_sq_eq_prime_iff_of_mod_four_eq_three`.

We also prove the supplementary laws that give conditions for when `-1` or `2`
(or `-2`) is a square modulo a prime `p`:
`legendre_sym.at_neg_one` and `zmod.exists_sq_eq_neg_one_iff` for `-1`,
`legendre_sym.at_two` and `zmod.exists_sq_eq_two_iff` for `2`,
`legendre_sym.at_neg_two` and `zmod.exists_sq_eq_neg_two_iff` for `-2`.

## Implementation notes

The proofs use results for quadratic characters on arbitrary finite fields
from `number_theory.legendre_symbol.quadratic_char`, which in turn are based on
properties of quadratic Gauss sums as provided by `number_theory.legendre_symbol.gauss_sum`.

## Tags

quadratic residue, quadratic nonresidue, Legendre symbol, quadratic reciprocity
-/


open Nat

section Euler

namespace Zmod

variable (p : ℕ) [Fact p.Prime]

/-- Euler's Criterion: A unit `x` of `zmod p` is a square if and only if `x ^ (p / 2) = 1`. -/
theorem euler_criterion_units (x : (Zmod p)ˣ) : (∃ y : (Zmod p)ˣ, y ^ 2 = x) ↔ x ^ (p / 2) = 1 :=
  by
  by_cases hc : p = 2
  · subst hc
    simp only [eq_iff_true_of_subsingleton, exists_const]
  · have h₀ := FiniteField.unit_is_square_iff (by rwa [ring_char_zmod_n]) x
    have hs : (∃ y : (Zmod p)ˣ, y ^ 2 = x) ↔ IsSquare x :=
      by
      rw [isSquare_iff_exists_sq x]
      simp_rw [eq_comm]
    rw [hs]
    rwa [card p] at h₀
#align zmod.euler_criterion_units Zmod.euler_criterion_units

/-- Euler's Criterion: a nonzero `a : zmod p` is a square if and only if `x ^ (p / 2) = 1`. -/
theorem euler_criterion {a : Zmod p} (ha : a ≠ 0) : IsSquare (a : Zmod p) ↔ a ^ (p / 2) = 1 :=
  by
  apply (iff_congr _ (by simp [Units.ext_iff])).mp (euler_criterion_units p (Units.mk0 a ha))
  simp only [Units.ext_iff, sq, Units.val_mk0, Units.val_mul]
  constructor;
  · rintro ⟨y, hy⟩
    exact ⟨y, hy.symm⟩
  · rintro ⟨y, rfl⟩
    have hy : y ≠ 0 := by
      rintro rfl
      simpa [zero_pow] using ha
    refine' ⟨Units.mk0 y hy, _⟩
    simp
#align zmod.euler_criterion Zmod.euler_criterion

/-- If `a : zmod p` is nonzero, then `a^(p/2)` is either `1` or `-1`. -/
theorem pow_div_two_eq_neg_one_or_one {a : Zmod p} (ha : a ≠ 0) :
    a ^ (p / 2) = 1 ∨ a ^ (p / 2) = -1 :=
  by
  cases' prime.eq_two_or_odd (Fact.out p.prime) with hp2 hp_odd
  · subst p
    revert a ha
    decide
  rw [← mul_self_eq_one_iff, ← pow_add, ← two_mul, two_mul_odd_div_two hp_odd]
  exact pow_card_sub_one_eq_one ha
#align zmod.pow_div_two_eq_neg_one_or_one Zmod.pow_div_two_eq_neg_one_or_one

end Zmod

end Euler

section Legendre

/-!
### Definition of the Legendre symbol and basic properties
-/


open Zmod

variable (p : ℕ) [Fact p.Prime]

/-- The Legendre symbol of `a : ℤ` and a prime `p`, `legendre_sym p a`,
is an integer defined as

* `0` if `a` is `0` modulo `p`;
* `1` if `a` is a nonzero square modulo `p`
* `-1` otherwise.

Note the order of the arguments! The advantage of the order chosen here is
that `legendre_sym p` is a multiplicative function `ℤ → ℤ`.
-/
def legendreSym (a : ℤ) : ℤ :=
  quadraticChar (Zmod p) a
#align legendre_sym legendreSym

namespace legendreSym

/-- We have the congruence `legendre_sym p a ≡ a ^ (p / 2) mod p`. -/
theorem eq_pow (a : ℤ) : (legendreSym p a : Zmod p) = a ^ (p / 2) :=
  by
  cases' eq_or_ne (ringChar (Zmod p)) 2 with hc hc
  · by_cases ha : (a : Zmod p) = 0
    · rw [legendreSym, ha, quadratic_char_zero,
        zero_pow (Nat.div_pos (Fact.out p.prime).two_le (succ_pos 1))]
      norm_cast
    · have := (ring_char_zmod_n p).symm.trans hc
      -- p = 2
      subst p
      rw [legendreSym, quadratic_char_eq_one_of_char_two hc ha]
      revert ha
      generalize (a : Zmod 2) = b
      revert b
      decide
  · convert quadratic_char_eq_pow_of_char_ne_two' hc (a : Zmod p)
    exact (card p).symm
#align legendre_sym.eq_pow legendreSym.eq_pow

/-- If `p ∤ a`, then `legendre_sym p a` is `1` or `-1`. -/
theorem eq_one_or_neg_one {a : ℤ} (ha : (a : Zmod p) ≠ 0) :
    legendreSym p a = 1 ∨ legendreSym p a = -1 :=
  quadratic_char_dichotomy ha
#align legendre_sym.eq_one_or_neg_one legendreSym.eq_one_or_neg_one

theorem eq_neg_one_iff_not_one {a : ℤ} (ha : (a : Zmod p) ≠ 0) :
    legendreSym p a = -1 ↔ ¬legendreSym p a = 1 :=
  quadratic_char_eq_neg_one_iff_not_one ha
#align legendre_sym.eq_neg_one_iff_not_one legendreSym.eq_neg_one_iff_not_one

/-- The Legendre symbol of `p` and `a` is zero iff `p ∣ a`. -/
theorem eq_zero_iff (a : ℤ) : legendreSym p a = 0 ↔ (a : Zmod p) = 0 :=
  quadratic_char_eq_zero_iff
#align legendre_sym.eq_zero_iff legendreSym.eq_zero_iff

@[simp]
theorem at_zero : legendreSym p 0 = 0 := by rw [legendreSym, Int.cast_zero, MulChar.map_zero]
#align legendre_sym.at_zero legendreSym.at_zero

@[simp]
theorem at_one : legendreSym p 1 = 1 := by rw [legendreSym, Int.cast_one, MulChar.map_one]
#align legendre_sym.at_one legendreSym.at_one

/-- The Legendre symbol is multiplicative in `a` for `p` fixed. -/
protected theorem mul (a b : ℤ) : legendreSym p (a * b) = legendreSym p a * legendreSym p b := by
  simp only [legendreSym, Int.cast_mul, map_mul]
#align legendre_sym.mul legendreSym.mul

/-- The Legendre symbol is a homomorphism of monoids with zero. -/
@[simps]
def hom : ℤ →*₀ ℤ where
  toFun := legendreSym p
  map_zero' := at_zero p
  map_one' := at_one p
  map_mul' := legendreSym.mul p
#align legendre_sym.hom legendreSym.hom

/-- The square of the symbol is 1 if `p ∤ a`. -/
theorem sq_one {a : ℤ} (ha : (a : Zmod p) ≠ 0) : legendreSym p a ^ 2 = 1 :=
  quadratic_char_sq_one ha
#align legendre_sym.sq_one legendreSym.sq_one

/-- The Legendre symbol of `a^2` at `p` is 1 if `p ∤ a`. -/
theorem sq_one' {a : ℤ} (ha : (a : Zmod p) ≠ 0) : legendreSym p (a ^ 2) = 1 := by
  exact_mod_cast quadratic_char_sq_one' ha
#align legendre_sym.sq_one' legendreSym.sq_one'

/-- The Legendre symbol depends only on `a` mod `p`. -/
protected theorem mod (a : ℤ) : legendreSym p a = legendreSym p (a % p) := by
  simp only [legendreSym, int_cast_mod]
#align legendre_sym.mod legendreSym.mod

/-- When `p ∤ a`, then `legendre_sym p a = 1` iff `a` is a square mod `p`. -/
theorem eq_one_iff {a : ℤ} (ha0 : (a : Zmod p) ≠ 0) : legendreSym p a = 1 ↔ IsSquare (a : Zmod p) :=
  quadratic_char_one_iff_is_square ha0
#align legendre_sym.eq_one_iff legendreSym.eq_one_iff

theorem eq_one_iff' {a : ℕ} (ha0 : (a : Zmod p) ≠ 0) :
    legendreSym p a = 1 ↔ IsSquare (a : Zmod p) :=
  by
  rw [eq_one_iff]
  norm_cast
  exact_mod_cast ha0
#align legendre_sym.eq_one_iff' legendreSym.eq_one_iff'

/-- `legendre_sym p a = -1` iff `a` is a nonsquare mod `p`. -/
theorem eq_neg_one_iff {a : ℤ} : legendreSym p a = -1 ↔ ¬IsSquare (a : Zmod p) :=
  quadratic_char_neg_one_iff_not_is_square
#align legendre_sym.eq_neg_one_iff legendreSym.eq_neg_one_iff

theorem eq_neg_one_iff' {a : ℕ} : legendreSym p a = -1 ↔ ¬IsSquare (a : Zmod p) :=
  by
  rw [eq_neg_one_iff]
  norm_cast
#align legendre_sym.eq_neg_one_iff' legendreSym.eq_neg_one_iff'

/-- The number of square roots of `a` modulo `p` is determined by the Legendre symbol. -/
theorem card_sqrts (hp : p ≠ 2) (a : ℤ) :
    ↑{ x : Zmod p | x ^ 2 = a }.toFinset.card = legendreSym p a + 1 :=
  quadratic_char_card_sqrts ((ring_char_zmod_n p).substr hp) a
#align legendre_sym.card_sqrts legendreSym.card_sqrts

end legendreSym

end Legendre

section Values

/-!
### The value of the Legendre symbol at `-1`

See `jacobi_sym.at_neg_one` for the corresponding statement for the Jacobi symbol.
-/


variable {p : ℕ} [Fact p.Prime]

open Zmod

/-- `legendre_sym p (-1)` is given by `χ₄ p`. -/
theorem legendreSym.at_neg_one (hp : p ≠ 2) : legendreSym p (-1) = χ₄ p := by
  simp only [legendreSym, card p, quadratic_char_neg_one ((ring_char_zmod_n p).substr hp),
    Int.cast_neg, Int.cast_one]
#align legendre_sym.at_neg_one legendreSym.at_neg_one

namespace Zmod

/-- `-1` is a square in `zmod p` iff `p` is not congruent to `3` mod `4`. -/
theorem exists_sq_eq_neg_one_iff : IsSquare (-1 : Zmod p) ↔ p % 4 ≠ 3 := by
  rw [FiniteField.is_square_neg_one_iff, card p]
#align zmod.exists_sq_eq_neg_one_iff Zmod.exists_sq_eq_neg_one_iff

theorem mod_four_ne_three_of_sq_eq_neg_one {y : Zmod p} (hy : y ^ 2 = -1) : p % 4 ≠ 3 :=
  exists_sq_eq_neg_one_iff.1 ⟨y, hy ▸ pow_two y⟩
#align zmod.mod_four_ne_three_of_sq_eq_neg_one Zmod.mod_four_ne_three_of_sq_eq_neg_one

/-- If two nonzero squares are negatives of each other in `zmod p`, then `p % 4 ≠ 3`. -/
theorem mod_four_ne_three_of_sq_eq_neg_sq' {x y : Zmod p} (hy : y ≠ 0) (hxy : x ^ 2 = -y ^ 2) :
    p % 4 ≠ 3 :=
  @mod_four_ne_three_of_sq_eq_neg_one p _ (x / y)
    (by
      apply_fun fun z => z / y ^ 2  at hxy
      rwa [neg_div, ← div_pow, ← div_pow, div_self hy, one_pow] at hxy)
#align zmod.mod_four_ne_three_of_sq_eq_neg_sq' Zmod.mod_four_ne_three_of_sq_eq_neg_sq'

theorem mod_four_ne_three_of_sq_eq_neg_sq {x y : Zmod p} (hx : x ≠ 0) (hxy : x ^ 2 = -y ^ 2) :
    p % 4 ≠ 3 :=
  mod_four_ne_three_of_sq_eq_neg_sq' hx (eq_neg_iff_eq_neg.1 hxy)
#align zmod.mod_four_ne_three_of_sq_eq_neg_sq Zmod.mod_four_ne_three_of_sq_eq_neg_sq

end Zmod

/-!
### The value of the Legendre symbol at `2` and `-2`

See `jacobi_sym.at_two` and `jacobi_sym.at_neg_two` for the corresponding statements
for the Jacobi symbol.
-/


namespace legendreSym

variable (hp : p ≠ 2)

include hp

/-- `legendre_sym p 2` is given by `χ₈ p`. -/
theorem at_two : legendreSym p 2 = χ₈ p := by
  simp only [legendreSym, card p, quadratic_char_two ((ring_char_zmod_n p).substr hp),
    Int.cast_bit0, Int.cast_one]
#align legendre_sym.at_two legendreSym.at_two

/-- `legendre_sym p (-2)` is given by `χ₈' p`. -/
theorem at_neg_two : legendreSym p (-2) = χ₈' p := by
  simp only [legendreSym, card p, quadratic_char_neg_two ((ring_char_zmod_n p).substr hp),
    Int.cast_bit0, Int.cast_one, Int.cast_neg]
#align legendre_sym.at_neg_two legendreSym.at_neg_two

end legendreSym

namespace Zmod

variable (hp : p ≠ 2)

include hp

/-- `2` is a square modulo an odd prime `p` iff `p` is congruent to `1` or `7` mod `8`. -/
theorem exists_sq_eq_two_iff : IsSquare (2 : Zmod p) ↔ p % 8 = 1 ∨ p % 8 = 7 :=
  by
  rw [FiniteField.is_square_two_iff, card p]
  have h₁ := prime.mod_two_eq_one_iff_ne_two.mpr hp
  rw [← mod_mod_of_dvd p (by norm_num : 2 ∣ 8)] at h₁
  have h₂ := mod_lt p (by norm_num : 0 < 8)
  revert h₂ h₁
  generalize hm : p % 8 = m; clear! p
  decide!
#align zmod.exists_sq_eq_two_iff Zmod.exists_sq_eq_two_iff

/-- `-2` is a square modulo an odd prime `p` iff `p` is congruent to `1` or `3` mod `8`. -/
theorem exists_sq_eq_neg_two_iff : IsSquare (-2 : Zmod p) ↔ p % 8 = 1 ∨ p % 8 = 3 :=
  by
  rw [FiniteField.is_square_neg_two_iff, card p]
  have h₁ := prime.mod_two_eq_one_iff_ne_two.mpr hp
  rw [← mod_mod_of_dvd p (by norm_num : 2 ∣ 8)] at h₁
  have h₂ := mod_lt p (by norm_num : 0 < 8)
  revert h₂ h₁
  generalize hm : p % 8 = m; clear! p
  decide!
#align zmod.exists_sq_eq_neg_two_iff Zmod.exists_sq_eq_neg_two_iff

end Zmod

end Values

section Reciprocity

/-!
### The Law of Quadratic Reciprocity

See `jacobi_sym.quadratic_reciprocity` and variants for a version of Quadratic Reciprocity
for the Jacobi symbol.
-/


variable {p q : ℕ} [Fact p.Prime] [Fact q.Prime]

namespace legendreSym

open Zmod

/-- The Law of Quadratic Reciprocity: if `p` and `q` are distinct odd primes, then
`(q / p) * (p / q) = (-1)^((p-1)(q-1)/4)`. -/
theorem quadratic_reciprocity (hp : p ≠ 2) (hq : q ≠ 2) (hpq : p ≠ q) :
    legendreSym q p * legendreSym p q = (-1) ^ (p / 2 * (q / 2)) :=
  by
  have hp₁ := (prime.eq_two_or_odd <| Fact.out p.prime).resolve_left hp
  have hq₁ := (prime.eq_two_or_odd <| Fact.out q.prime).resolve_left hq
  have hq₂ := (ring_char_zmod_n q).substr hq
  have h :=
    quadratic_char_odd_prime ((ring_char_zmod_n p).substr hp) hq ((ring_char_zmod_n p).substr hpq)
  rw [card p] at h
  have nc : ∀ n r : ℕ, ((n : ℤ) : Zmod r) = n := fun n r => by norm_cast
  have nc' : (((-1) ^ (p / 2) : ℤ) : Zmod q) = (-1) ^ (p / 2) := by norm_cast
  rw [legendreSym, legendreSym, nc, nc, h, map_mul, mul_rotate', mul_comm (p / 2), ← pow_two,
    quadratic_char_sq_one (prime_ne_zero q p hpq.symm), mul_one, pow_mul, χ₄_eq_neg_one_pow hp₁,
    nc', map_pow, quadratic_char_neg_one hq₂, card q, χ₄_eq_neg_one_pow hq₁]
#align legendre_sym.quadratic_reciprocity legendreSym.quadratic_reciprocity

/-- The Law of Quadratic Reciprocity: if `p` and `q` are odd primes, then
`(q / p) = (-1)^((p-1)(q-1)/4) * (p / q)`. -/
theorem quadratic_reciprocity' (hp : p ≠ 2) (hq : q ≠ 2) :
    legendreSym q p = (-1) ^ (p / 2 * (q / 2)) * legendreSym p q :=
  by
  cases' eq_or_ne p q with h h
  · subst p
    rw [(eq_zero_iff q q).mpr (by exact_mod_cast nat_cast_self q), mul_zero]
  · have qr := congr_arg (· * legendreSym p q) (quadratic_reciprocity hp hq h)
    have : ((q : ℤ) : Zmod p) ≠ 0 := by exact_mod_cast prime_ne_zero p q h
    simpa only [mul_assoc, ← pow_two, sq_one p this, mul_one] using qr
#align legendre_sym.quadratic_reciprocity' legendreSym.quadratic_reciprocity'

/-- The Law of Quadratic Reciprocity: if `p` and `q` are odd primes and `p % 4 = 1`,
then `(q / p) = (p / q)`. -/
theorem quadratic_reciprocity_one_mod_four (hp : p % 4 = 1) (hq : q ≠ 2) :
    legendreSym q p = legendreSym p q := by
  rw [quadratic_reciprocity' (prime.mod_two_eq_one_iff_ne_two.mp (odd_of_mod_four_eq_one hp)) hq,
    pow_mul, neg_one_pow_div_two_of_one_mod_four hp, one_pow, one_mul]
#align
  legendre_sym.quadratic_reciprocity_one_mod_four legendreSym.quadratic_reciprocity_one_mod_four

/-- The Law of Quadratic Reciprocity: if `p` and `q` are primes that are both congruent
to `3` mod `4`, then `(q / p) = -(p / q)`. -/
theorem quadratic_reciprocity_three_mod_four (hp : p % 4 = 3) (hq : q % 4 = 3) :
    legendreSym q p = -legendreSym p q :=
  by
  let nop := @neg_one_pow_div_two_of_three_mod_four
  rw [quadratic_reciprocity', pow_mul, nop hp, nop hq, neg_one_mul] <;>
    rwa [← prime.mod_two_eq_one_iff_ne_two, odd_of_mod_four_eq_three]
#align
  legendre_sym.quadratic_reciprocity_three_mod_four legendreSym.quadratic_reciprocity_three_mod_four

end legendreSym

namespace Zmod

open legendreSym

/-- If `p` and `q` are odd primes and `p % 4 = 1`, then `q` is a square mod `p` iff
`p` is a square mod `q`. -/
theorem exists_sq_eq_prime_iff_of_mod_four_eq_one (hp1 : p % 4 = 1) (hq1 : q ≠ 2) :
    IsSquare (q : Zmod p) ↔ IsSquare (p : Zmod q) :=
  by
  cases' eq_or_ne p q with h h
  · subst p
  ·
    rw [← eq_one_iff' p (prime_ne_zero p q h), ← eq_one_iff' q (prime_ne_zero q p h.symm),
      quadratic_reciprocity_one_mod_four hp1 hq1]
#align zmod.exists_sq_eq_prime_iff_of_mod_four_eq_one Zmod.exists_sq_eq_prime_iff_of_mod_four_eq_one

/-- If `p` and `q` are distinct primes that are both congruent to `3` mod `4`, then `q` is
a square mod `p` iff `p` is a nonsquare mod `q`. -/
theorem exists_sq_eq_prime_iff_of_mod_four_eq_three (hp3 : p % 4 = 3) (hq3 : q % 4 = 3)
    (hpq : p ≠ q) : IsSquare (q : Zmod p) ↔ ¬IsSquare (p : Zmod q) := by
  rw [← eq_one_iff' p (prime_ne_zero p q hpq), ← eq_neg_one_iff' q,
    quadratic_reciprocity_three_mod_four hp3 hq3, neg_inj]
#align
  zmod.exists_sq_eq_prime_iff_of_mod_four_eq_three Zmod.exists_sq_eq_prime_iff_of_mod_four_eq_three

end Zmod

end Reciprocity

