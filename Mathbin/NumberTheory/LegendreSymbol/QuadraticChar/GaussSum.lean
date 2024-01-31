/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import NumberTheory.LegendreSymbol.QuadraticChar.Basic
import NumberTheory.LegendreSymbol.GaussSum

#align_import number_theory.legendre_symbol.quadratic_char.gauss_sum from "leanprover-community/mathlib"@"08b63ab58a6ec1157ebeafcbbe6c7a3fb3c9f6d5"

/-!
# Quadratic characters of finite fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

Further facts relying on Gauss sums.

-/


/-!
### Basic properties of the quadratic character

We prove some properties of the quadratic character.
We work with a finite field `F` here.
The interesting case is when the characteristic of `F` is odd.
-/


section SpecialValues

open ZMod MulChar

variable {F : Type _} [Field F] [Fintype F]

#print quadraticChar_two /-
/-- The value of the quadratic character at `2` -/
theorem quadraticChar_two [DecidableEq F] (hF : ringChar F ≠ 2) :
    quadraticChar F 2 = χ₈ (Fintype.card F) :=
  IsQuadratic.eq_of_eq_coe (quadraticChar_isQuadratic F) isQuadratic_χ₈ hF
    ((quadraticChar_eq_pow_of_char_ne_two' hF 2).trans (FiniteField.two_pow_card hF))
#align quadratic_char_two quadraticChar_two
-/

#print FiniteField.isSquare_two_iff /-
/-- `2` is a square in `F` iff `#F` is not congruent to `3` or `5` mod `8`. -/
theorem FiniteField.isSquare_two_iff :
    IsSquare (2 : F) ↔ Fintype.card F % 8 ≠ 3 ∧ Fintype.card F % 8 ≠ 5 := by classical
#align finite_field.is_square_two_iff FiniteField.isSquare_two_iff
-/

#print quadraticChar_neg_two /-
/-- The value of the quadratic character at `-2` -/
theorem quadraticChar_neg_two [DecidableEq F] (hF : ringChar F ≠ 2) :
    quadraticChar F (-2) = χ₈' (Fintype.card F) := by
  rw [(by norm_num : (-2 : F) = -1 * 2), map_mul, χ₈'_eq_χ₄_mul_χ₈, quadraticChar_neg_one hF,
    quadraticChar_two hF, @cast_nat_cast _ (ZMod 4) _ _ _ (by norm_num : 4 ∣ 8)]
#align quadratic_char_neg_two quadraticChar_neg_two
-/

#print FiniteField.isSquare_neg_two_iff /-
/-- `-2` is a square in `F` iff `#F` is not congruent to `5` or `7` mod `8`. -/
theorem FiniteField.isSquare_neg_two_iff :
    IsSquare (-2 : F) ↔ Fintype.card F % 8 ≠ 5 ∧ Fintype.card F % 8 ≠ 7 := by classical
#align finite_field.is_square_neg_two_iff FiniteField.isSquare_neg_two_iff
-/

#print quadraticChar_card_card /-
/-- The relation between the values of the quadratic character of one field `F` at the
cardinality of another field `F'` and of the quadratic character of `F'` at the cardinality
of `F`. -/
theorem quadraticChar_card_card [DecidableEq F] (hF : ringChar F ≠ 2) {F' : Type _} [Field F']
    [Fintype F'] [DecidableEq F'] (hF' : ringChar F' ≠ 2) (h : ringChar F' ≠ ringChar F) :
    quadraticChar F (Fintype.card F') = quadraticChar F' (quadraticChar F (-1) * Fintype.card F) :=
  by
  let χ := (quadraticChar F).ringHomComp (algebraMap ℤ F')
  have hχ₁ : χ.is_nontrivial :=
    by
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one hF
    have hu : IsUnit a := by
      contrapose ha
      exact ne_of_eq_of_ne (map_nonunit (quadraticChar F) ha) (mt zero_eq_neg.mp one_ne_zero)
    use hu.unit
    simp only [IsUnit.unit_spec, ring_hom_comp_apply, eq_intCast, Ne.def, ha]
    rw [Int.cast_neg, Int.cast_one]
    exact Ring.neg_one_ne_one_of_char_ne_two hF'
  have hχ₂ : χ.is_quadratic := is_quadratic.comp (quadraticChar_isQuadratic F) _
  have h := Char.card_pow_card hχ₁ hχ₂ h hF'
  rw [← quadraticChar_eq_pow_of_char_ne_two' hF'] at h 
  exact
    (is_quadratic.eq_of_eq_coe (quadraticChar_isQuadratic F') (quadraticChar_isQuadratic F) hF'
        h).symm
#align quadratic_char_card_card quadraticChar_card_card
-/

#print quadraticChar_odd_prime /-
/-- The value of the quadratic character at an odd prime `p` different from `ring_char F`. -/
theorem quadraticChar_odd_prime [DecidableEq F] (hF : ringChar F ≠ 2) {p : ℕ} [Fact p.Prime]
    (hp₁ : p ≠ 2) (hp₂ : ringChar F ≠ p) :
    quadraticChar F p = quadraticChar (ZMod p) (χ₄ (Fintype.card F) * Fintype.card F) :=
  by
  rw [← quadraticChar_neg_one hF]
  have h :=
    quadraticChar_card_card hF (ne_of_eq_of_ne (ring_char_zmod_n p) hp₁)
      (ne_of_eq_of_ne (ring_char_zmod_n p) hp₂.symm)
  rwa [card p] at h 
#align quadratic_char_odd_prime quadraticChar_odd_prime
-/

#print FiniteField.isSquare_odd_prime_iff /-
/-- An odd prime `p` is a square in `F` iff the quadratic character of `zmod p` does not
take the value `-1` on `χ₄(#F) * #F`. -/
theorem FiniteField.isSquare_odd_prime_iff (hF : ringChar F ≠ 2) {p : ℕ} [Fact p.Prime]
    (hp : p ≠ 2) :
    IsSquare (p : F) ↔ quadraticChar (ZMod p) (χ₄ (Fintype.card F) * Fintype.card F) ≠ -1 := by
  classical
#align finite_field.is_square_odd_prime_iff FiniteField.isSquare_odd_prime_iff
-/

end SpecialValues

