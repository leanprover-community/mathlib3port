/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Data.Fintype.Parity
import NumberTheory.LegendreSymbol.ZmodChar
import FieldTheory.Finite.Basic

#align_import number_theory.legendre_symbol.quadratic_char.basic from "leanprover-community/mathlib"@"e160cefedc932ce41c7049bf0c4b0f061d06216e"

/-!
# Quadratic characters of finite fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the quadratic character on a finite field `F` and proves
some basic statements about it.

## Tags

quadratic character
-/


/-!
### Definition of the quadratic character

We define the quadratic character of a finite field `F` with values in ℤ.
-/


section Define

#print quadraticCharFun /-
/-- Define the quadratic character with values in ℤ on a monoid with zero `α`.
It takes the value zero at zero; for non-zero argument `a : α`, it is `1`
if `a` is a square, otherwise it is `-1`.

This only deserves the name "character" when it is multiplicative,
e.g., when `α` is a finite field. See `quadratic_char_fun_mul`.

We will later define `quadratic_char` to be a multiplicative character
of type `mul_char F ℤ`, when the domain is a finite field `F`.
-/
def quadraticCharFun (α : Type _) [MonoidWithZero α] [DecidableEq α]
    [DecidablePred (IsSquare : α → Prop)] (a : α) : ℤ :=
  if a = 0 then 0 else if IsSquare a then 1 else -1
#align quadratic_char_fun quadraticCharFun
-/

end Define

/-!
### Basic properties of the quadratic character

We prove some properties of the quadratic character.
We work with a finite field `F` here.
The interesting case is when the characteristic of `F` is odd.
-/


section quadraticChar

open MulChar

variable {F : Type _} [Field F] [Fintype F] [DecidableEq F]

#print quadraticCharFun_eq_zero_iff /-
/-- Some basic API lemmas -/
theorem quadraticCharFun_eq_zero_iff {a : F} : quadraticCharFun F a = 0 ↔ a = 0 :=
  by
  simp only [quadraticCharFun]
  by_cases ha : a = 0
  · simp only [ha, eq_self_iff_true, if_true]
  · simp only [ha, if_false, iff_false_iff]
    split_ifs <;> simp only [neg_eq_zero, one_ne_zero, not_false_iff]
#align quadratic_char_fun_eq_zero_iff quadraticCharFun_eq_zero_iff
-/

#print quadraticCharFun_zero /-
@[simp]
theorem quadraticCharFun_zero : quadraticCharFun F 0 = 0 := by
  simp only [quadraticCharFun, eq_self_iff_true, if_true, id.def]
#align quadratic_char_fun_zero quadraticCharFun_zero
-/

#print quadraticCharFun_one /-
@[simp]
theorem quadraticCharFun_one : quadraticCharFun F 1 = 1 := by
  simp only [quadraticCharFun, one_ne_zero, isSquare_one, if_true, if_false, id.def]
#align quadratic_char_fun_one quadraticCharFun_one
-/

#print quadraticCharFun_eq_one_of_char_two /-
/-- If `ring_char F = 2`, then `quadratic_char_fun F` takes the value `1` on nonzero elements. -/
theorem quadraticCharFun_eq_one_of_char_two (hF : ringChar F = 2) {a : F} (ha : a ≠ 0) :
    quadraticCharFun F a = 1 :=
  by
  simp only [quadraticCharFun, ha, if_false, ite_eq_left_iff]
  exact fun h => False.ndrec _ (h (FiniteField.isSquare_of_char_two hF a))
#align quadratic_char_fun_eq_one_of_char_two quadraticCharFun_eq_one_of_char_two
-/

#print quadraticCharFun_eq_pow_of_char_ne_two /-
/-- If `ring_char F` is odd, then `quadratic_char_fun F a` can be computed in
terms of `a ^ (fintype.card F / 2)`. -/
theorem quadraticCharFun_eq_pow_of_char_ne_two (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    quadraticCharFun F a = if a ^ (Fintype.card F / 2) = 1 then 1 else -1 :=
  by
  simp only [quadraticCharFun, ha, if_false]
  simp_rw [FiniteField.isSquare_iff hF ha]
#align quadratic_char_fun_eq_pow_of_char_ne_two quadraticCharFun_eq_pow_of_char_ne_two
-/

#print quadraticCharFun_mul /-
/-- The quadratic character is multiplicative. -/
theorem quadraticCharFun_mul (a b : F) :
    quadraticCharFun F (a * b) = quadraticCharFun F a * quadraticCharFun F b :=
  by
  by_cases ha : a = 0
  · rw [ha, MulZeroClass.zero_mul, quadraticCharFun_zero, MulZeroClass.zero_mul]
  -- now `a ≠ 0`
  by_cases hb : b = 0
  · rw [hb, MulZeroClass.mul_zero, quadraticCharFun_zero, MulZeroClass.mul_zero]
  -- now `a ≠ 0` and `b ≠ 0`
  have hab := mul_ne_zero ha hb
  by_cases hF : ringChar F = 2
  ·-- case `ring_char F = 2`
    rw [quadraticCharFun_eq_one_of_char_two hF ha, quadraticCharFun_eq_one_of_char_two hF hb,
      quadraticCharFun_eq_one_of_char_two hF hab, mul_one]
  · -- case of odd characteristic
    rw [quadraticCharFun_eq_pow_of_char_ne_two hF ha, quadraticCharFun_eq_pow_of_char_ne_two hF hb,
      quadraticCharFun_eq_pow_of_char_ne_two hF hab, mul_pow]
    cases' FiniteField.pow_dichotomy hF hb with hb' hb'
    · simp only [hb', mul_one, eq_self_iff_true, if_true]
    · have h := Ring.neg_one_ne_one_of_char_ne_two hF
      -- `-1 ≠ 1`
      simp only [hb', h, mul_neg, mul_one, if_false, ite_mul, neg_mul]
      cases' FiniteField.pow_dichotomy hF ha with ha' ha' <;>
        simp only [ha', h, neg_neg, eq_self_iff_true, if_true, if_false]
#align quadratic_char_fun_mul quadraticCharFun_mul
-/

variable (F)

#print quadraticChar /-
/-- The quadratic character as a multiplicative character. -/
@[simps]
def quadraticChar : MulChar F ℤ where
  toFun := quadraticCharFun F
  map_one' := quadraticCharFun_one
  map_mul' := quadraticCharFun_mul
  map_nonunit' a ha := by rw [of_not_not (mt Ne.isUnit ha)]; exact quadraticCharFun_zero
#align quadratic_char quadraticChar
-/

variable {F}

#print quadraticChar_eq_zero_iff /-
/-- The value of the quadratic character on `a` is zero iff `a = 0`. -/
theorem quadraticChar_eq_zero_iff {a : F} : quadraticChar F a = 0 ↔ a = 0 :=
  quadraticCharFun_eq_zero_iff
#align quadratic_char_eq_zero_iff quadraticChar_eq_zero_iff
-/

#print quadraticChar_zero /-
@[simp]
theorem quadraticChar_zero : quadraticChar F 0 = 0 := by
  simp only [quadraticChar_apply, quadraticCharFun_zero]
#align quadratic_char_zero quadraticChar_zero
-/

#print quadraticChar_one_iff_isSquare /-
/-- For nonzero `a : F`, `quadratic_char F a = 1 ↔ is_square a`. -/
theorem quadraticChar_one_iff_isSquare {a : F} (ha : a ≠ 0) : quadraticChar F a = 1 ↔ IsSquare a :=
  by
  simp only [quadraticChar_apply, quadraticCharFun, ha, (by decide : (-1 : ℤ) ≠ 1), if_false,
    ite_eq_left_iff, imp_false, Classical.not_not]
#align quadratic_char_one_iff_is_square quadraticChar_one_iff_isSquare
-/

#print quadraticChar_sq_one' /-
/-- The quadratic character takes the value `1` on nonzero squares. -/
theorem quadraticChar_sq_one' {a : F} (ha : a ≠ 0) : quadraticChar F (a ^ 2) = 1 := by
  simp only [quadraticCharFun, ha, pow_eq_zero_iff, Nat.succ_pos', IsSquare_sq, if_true, if_false,
    quadraticChar_apply]
#align quadratic_char_sq_one' quadraticChar_sq_one'
-/

#print quadraticChar_sq_one /-
/-- The square of the quadratic character on nonzero arguments is `1`. -/
theorem quadraticChar_sq_one {a : F} (ha : a ≠ 0) : quadraticChar F a ^ 2 = 1 := by
  rwa [pow_two, ← map_mul, ← pow_two, quadraticChar_sq_one']
#align quadratic_char_sq_one quadraticChar_sq_one
-/

#print quadraticChar_dichotomy /-
/-- The quadratic character is `1` or `-1` on nonzero arguments. -/
theorem quadraticChar_dichotomy {a : F} (ha : a ≠ 0) :
    quadraticChar F a = 1 ∨ quadraticChar F a = -1 :=
  sq_eq_one_iff.1 <| quadraticChar_sq_one ha
#align quadratic_char_dichotomy quadraticChar_dichotomy
-/

#print quadraticChar_eq_neg_one_iff_not_one /-
/-- The quadratic character is `1` or `-1` on nonzero arguments. -/
theorem quadraticChar_eq_neg_one_iff_not_one {a : F} (ha : a ≠ 0) :
    quadraticChar F a = -1 ↔ ¬quadraticChar F a = 1 :=
  by
  refine' ⟨fun h => _, fun h₂ => (or_iff_right h₂).mp (quadraticChar_dichotomy ha)⟩
  rw [h]
  norm_num
#align quadratic_char_eq_neg_one_iff_not_one quadraticChar_eq_neg_one_iff_not_one
-/

#print quadraticChar_neg_one_iff_not_isSquare /-
/-- For `a : F`, `quadratic_char F a = -1 ↔ ¬ is_square a`. -/
theorem quadraticChar_neg_one_iff_not_isSquare {a : F} : quadraticChar F a = -1 ↔ ¬IsSquare a :=
  by
  by_cases ha : a = 0
  · simp only [ha, isSquare_zero, MulChar.map_zero, zero_eq_neg, one_ne_zero, not_true]
  · rw [quadraticChar_eq_neg_one_iff_not_one ha, quadraticChar_one_iff_isSquare ha]
#align quadratic_char_neg_one_iff_not_is_square quadraticChar_neg_one_iff_not_isSquare
-/

#print quadraticChar_exists_neg_one /-
/-- If `F` has odd characteristic, then `quadratic_char F` takes the value `-1`. -/
theorem quadraticChar_exists_neg_one (hF : ringChar F ≠ 2) : ∃ a, quadraticChar F a = -1 :=
  (FiniteField.exists_nonsquare hF).imp fun b h₁ => quadraticChar_neg_one_iff_not_isSquare.mpr h₁
#align quadratic_char_exists_neg_one quadraticChar_exists_neg_one
-/

#print quadraticChar_eq_one_of_char_two /-
/-- If `ring_char F = 2`, then `quadratic_char F` takes the value `1` on nonzero elements. -/
theorem quadraticChar_eq_one_of_char_two (hF : ringChar F = 2) {a : F} (ha : a ≠ 0) :
    quadraticChar F a = 1 :=
  quadraticCharFun_eq_one_of_char_two hF ha
#align quadratic_char_eq_one_of_char_two quadraticChar_eq_one_of_char_two
-/

#print quadraticChar_eq_pow_of_char_ne_two /-
/-- If `ring_char F` is odd, then `quadratic_char F a` can be computed in
terms of `a ^ (fintype.card F / 2)`. -/
theorem quadraticChar_eq_pow_of_char_ne_two (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    quadraticChar F a = if a ^ (Fintype.card F / 2) = 1 then 1 else -1 :=
  quadraticCharFun_eq_pow_of_char_ne_two hF ha
#align quadratic_char_eq_pow_of_char_ne_two quadraticChar_eq_pow_of_char_ne_two
-/

#print quadraticChar_eq_pow_of_char_ne_two' /-
theorem quadraticChar_eq_pow_of_char_ne_two' (hF : ringChar F ≠ 2) (a : F) :
    (quadraticChar F a : F) = a ^ (Fintype.card F / 2) :=
  by
  by_cases ha : a = 0
  · have : 0 < Fintype.card F / 2 := Nat.div_pos Fintype.one_lt_card two_pos
    simp only [ha, zero_pow this, quadraticChar_apply, quadraticChar_zero, Int.cast_zero]
  · rw [quadraticChar_eq_pow_of_char_ne_two hF ha]
    by_cases ha' : a ^ (Fintype.card F / 2) = 1
    · simp only [ha', eq_self_iff_true, if_true, Int.cast_one]
    · have ha'' := Or.resolve_left (FiniteField.pow_dichotomy hF ha) ha'
      simp only [ha'', Int.cast_ite, Int.cast_one, Int.cast_neg, ite_eq_right_iff]
      exact Eq.symm
#align quadratic_char_eq_pow_of_char_ne_two' quadraticChar_eq_pow_of_char_ne_two'
-/

variable (F)

#print quadraticChar_isQuadratic /-
/-- The quadratic character is quadratic as a multiplicative character. -/
theorem quadraticChar_isQuadratic : (quadraticChar F).IsQuadratic :=
  by
  intro a
  by_cases ha : a = 0
  · left; rw [ha]; exact quadraticChar_zero
  · right; exact quadraticChar_dichotomy ha
#align quadratic_char_is_quadratic quadraticChar_isQuadratic
-/

variable {F}

#print quadraticChar_isNontrivial /-
/-- The quadratic character is nontrivial as a multiplicative character
when the domain has odd characteristic. -/
theorem quadraticChar_isNontrivial (hF : ringChar F ≠ 2) : (quadraticChar F).IsNontrivial :=
  by
  rcases quadraticChar_exists_neg_one hF with ⟨a, ha⟩
  have hu : IsUnit a := by by_contra hf; rw [map_nonunit _ hf] at ha ; norm_num at ha 
  refine' ⟨hu.unit, (_ : quadraticChar F a ≠ 1)⟩
  rw [ha]
  norm_num
#align quadratic_char_is_nontrivial quadraticChar_isNontrivial
-/

#print quadraticChar_card_sqrts /-
/-- The number of solutions to `x^2 = a` is determined by the quadratic character. -/
theorem quadraticChar_card_sqrts (hF : ringChar F ≠ 2) (a : F) :
    ↑{x : F | x ^ 2 = a}.toFinset.card = quadraticChar F a + 1 :=
  by
  -- we consider the cases `a = 0`, `a` is a nonzero square and `a` is a nonsquare in turn
  by_cases h₀ : a = 0
  ·
    simp only [h₀, pow_eq_zero_iff, Nat.succ_pos', Int.ofNat_succ, Int.ofNat_zero, MulChar.map_zero,
      Set.setOf_eq_eq_singleton, Set.toFinset_card, Set.card_singleton]
  · set s := {x : F | x ^ 2 = a}.toFinset with hs
    by_cases h : IsSquare a
    · rw [(quadraticChar_one_iff_isSquare h₀).mpr h]
      rcases h with ⟨b, h⟩
      rw [h, mul_self_eq_zero] at h₀ 
      have h₁ : s = [b, -b].toFinset := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_univ, true_and_iff, List.toFinset_cons,
          List.toFinset_nil, insert_emptyc_eq, Finset.mem_insert, Finset.mem_singleton]
        rw [← pow_two] at h 
        simp only [hs, Set.mem_toFinset, Set.mem_setOf_eq, h]
        constructor
        · exact eq_or_eq_neg_of_sq_eq_sq _ _
        · rintro (h₂ | h₂) <;> rw [h₂]
          simp only [neg_sq]
      norm_cast
      rw [h₁, List.toFinset_cons, List.toFinset_cons, List.toFinset_nil]
      exact Finset.card_pair (Ne.symm (mt (Ring.eq_self_iff_eq_zero_of_char_ne_two hF).mp h₀))
    · rw [quadratic_char_neg_one_iff_not_is_square.mpr h]
      simp only [Int.coe_nat_eq_zero, Finset.card_eq_zero, Set.toFinset_card, Fintype.card_ofFinset,
        Set.mem_setOf_eq, add_left_neg]
      ext x
      simp only [iff_false_iff, Finset.mem_filter, Finset.mem_univ, true_and_iff,
        Finset.not_mem_empty]
      rw [isSquare_iff_exists_sq] at h 
      exact fun h' => h ⟨_, h'.symm⟩
#align quadratic_char_card_sqrts quadraticChar_card_sqrts
-/

open scoped BigOperators

#print quadraticChar_sum_zero /-
/-- The sum over the values of the quadratic character is zero when the characteristic is odd. -/
theorem quadraticChar_sum_zero (hF : ringChar F ≠ 2) : ∑ a : F, quadraticChar F a = 0 :=
  IsNontrivial.sum_eq_zero (quadraticChar_isNontrivial hF)
#align quadratic_char_sum_zero quadraticChar_sum_zero
-/

end quadraticChar

/-!
### Special values of the quadratic character

We express `quadratic_char F (-1)` in terms of `χ₄`.
-/


section SpecialValues

open ZMod MulChar

variable {F : Type _} [Field F] [Fintype F]

#print quadraticChar_neg_one /-
/-- The value of the quadratic character at `-1` -/
theorem quadraticChar_neg_one [DecidableEq F] (hF : ringChar F ≠ 2) :
    quadraticChar F (-1) = χ₄ (Fintype.card F) :=
  by
  have h := quadraticChar_eq_pow_of_char_ne_two hF (neg_ne_zero.mpr one_ne_zero)
  rw [h, χ₄_eq_neg_one_pow (FiniteField.odd_card_of_char_ne_two hF)]
  set n := Fintype.card F / 2
  cases' Nat.even_or_odd n with h₂ h₂
  · simp only [Even.neg_one_pow h₂, eq_self_iff_true, if_true]
  · simp only [Odd.neg_one_pow h₂, ite_eq_right_iff]
    exact fun hf => False.ndrec (1 = -1) (Ring.neg_one_ne_one_of_char_ne_two hF hf)
#align quadratic_char_neg_one quadraticChar_neg_one
-/

#print FiniteField.isSquare_neg_one_iff /-
/-- `-1` is a square in `F` iff `#F` is not congruent to `3` mod `4`. -/
theorem FiniteField.isSquare_neg_one_iff : IsSquare (-1 : F) ↔ Fintype.card F % 4 ≠ 3 := by
  classical
#align finite_field.is_square_neg_one_iff FiniteField.isSquare_neg_one_iff
-/

-- suggested by the linter (instead of `[decidable_eq F]`)
end SpecialValues

