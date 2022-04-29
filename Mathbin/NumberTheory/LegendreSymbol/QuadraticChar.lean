/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathbin.Tactic.Basic
import Mathbin.FieldTheory.Finite.Basic

/-!
# Quadratic characters of finite fields

This file defines the quadratic character on a finite field `F` and proves
some basic statements about it.

## Tags

quadratic character
-/


/-!
### Some general results on finite fields
-/


section General

/-- If `ring_char R = 2`, where `R` is a finite reduced commutative ring,
then every `a : R` is a square. -/
theorem is_square_of_char_two' {R : Type _} [Fintype R] [CommRingₓ R] [IsReduced R] [CharP R 2] (a : R) : IsSquare a :=
  (exists_imp_exists fun b h => pow_two b ▸ Eq.symm h) <|
    ((Fintype.bijective_iff_injective_and_card _).mpr ⟨frobenius_inj R 2, rfl⟩).Surjective a

namespace FiniteField

variable {F : Type _} [Field F] [Fintype F]

/-- In a finite field of characteristic `2`, all elements are squares. -/
theorem is_square_of_char_two (hF : ringChar F = 2) (a : F) : IsSquare a :=
  have hF' : CharP F 2 := ringChar.of_eq hF
  is_square_of_char_two' a

/-- If the finite field `F` has characteristic `≠ 2`, then it has odd cardinatlity. -/
theorem odd_card_of_char_ne_two (hF : ringChar F ≠ 2) : Fintype.card F % 2 = 1 := by
  rcases FiniteField.card F (ringChar F) with ⟨n, hp, h⟩
  have h₁ : Odd (ringChar F ^ (n : ℕ)) := Odd.pow ((or_iff_right hF).mp (Nat.Prime.eq_two_or_odd' hp))
  rwa [← h, Nat.odd_iff] at h₁

/-- Characteristic `≠ 2` implies that `-1 ≠ 1`. -/
theorem neg_one_ne_one_of_char_ne_two (hF : ringChar F ≠ 2) : (-1 : F) ≠ 1 := by
  have hc := CharP.char_is_prime F (ringChar F)
  have hF' : Fact (2 < ringChar F) := ⟨lt_of_le_of_neₓ (Nat.Prime.two_le hc) (Ne.symm hF)⟩
  exact CharP.neg_one_ne_one _ (ringChar F)

/-- If `F` has odd characteristic, then for nonzero `a : F`, we have that `a ^ (#F / 2) = ±1`. -/
theorem pow_dichotomy (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    a ^ (Fintype.card F / 2) = 1 ∨ a ^ (Fintype.card F / 2) = -1 := by
  have h₁ := FiniteField.pow_card_sub_one_eq_one a ha
  set q := Fintype.card F with hq
  have hq : q % 2 = 1 := FiniteField.odd_card_of_char_ne_two hF
  have h₂ := Nat.two_mul_odd_div_two hq
  rw [← h₂, mul_comm, pow_mulₓ, pow_two] at h₁
  exact mul_self_eq_one_iff.mp h₁

/-- A unit `a` of a finite field `F` of odd characteristic is a square
if and only if `a ^ (#F / 2) = 1`. -/
theorem unit_is_square_iff (hF : ringChar F ≠ 2) (a : Fˣ) : IsSquare a ↔ a ^ (Fintype.card F / 2) = 1 := by
  classical
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator Fˣ
  obtain ⟨n, hn⟩ : a ∈ Submonoid.powers g := by
    rw [mem_powers_iff_mem_zpowers]
    apply hg
  have hodd := Nat.two_mul_odd_div_two (FiniteField.odd_card_of_char_ne_two hF)
  constructor
  · rintro ⟨y, rfl⟩
    rw [← pow_two, ← pow_mulₓ, hodd]
    apply_fun @coe Fˣ F _
    · push_cast
      exact FiniteField.pow_card_sub_one_eq_one (y : F) (Units.ne_zero y)
      
    · exact Units.ext
      
    
  · subst a
    intro h
    have key : 2 * (Fintype.card F / 2) ∣ n * (Fintype.card F / 2) := by
      rw [← pow_mulₓ] at h
      rw [hodd, ← Fintype.card_units, ← order_of_eq_card_of_forall_mem_zpowers hg]
      apply order_of_dvd_of_pow_eq_one h
    have : 0 < Fintype.card F / 2 :=
      Nat.div_pos Fintype.one_lt_card
        (by
          norm_num)
    obtain ⟨m, rfl⟩ := Nat.dvd_of_mul_dvd_mul_rightₓ this key
    refine' ⟨g ^ m, _⟩
    rw [mul_comm, pow_mulₓ, pow_two]
    

/-- A non-zero `a : F` is a square if and only if `a ^ (#F / 2) = 1`. -/
theorem is_square_iff (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) : IsSquare a ↔ a ^ (Fintype.card F / 2) = 1 := by
  apply
    (iff_congr _
          (by
            simp [Units.ext_iff])).mp
      (FiniteField.unit_is_square_iff hF (Units.mk0 a ha))
  simp only [IsSquare, Units.ext_iff, Units.coe_mk0, Units.coe_mul]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, hy⟩
    
  · rintro ⟨y, rfl⟩
    have hy : y ≠ 0 := by
      rintro rfl
      simpa [zero_pow] using ha
    refine' ⟨Units.mk0 y hy, _⟩
    simp
    

/-- In a finite field of odd characteristic, not every element is a square. -/
theorem exists_nonsquare (hF : ringChar F ≠ 2) : ∃ a : F, ¬IsSquare a := by
  -- idea: the squaring map on `F` is not injetive, hence not surjective
  let sq : F → F := fun x => x ^ 2
  have h : ¬Function.Injective sq := by
    simp only [Function.Injective, not_forall, exists_prop]
    use -1, 1
    constructor
    · simp only [sq, one_pow, neg_one_sq]
      
    · exact FiniteField.neg_one_ne_one_of_char_ne_two hF
      
  have h₁ := mt fintype.injective_iff_surjective.mpr h
  -- sq not surjective
  push_neg  at h₁
  cases' h₁ with a h₁
  use a
  simp only [IsSquare, sq, not_exists, Ne.def] at h₁⊢
  intro b hb
  rw [← pow_two] at hb
  exact h₁ b hb.symm

end FiniteField

end General

namespace Charₓ

/-!
### Definition of the quadratic character

We define the quadratic character of a finite field `F` with values in ℤ.
-/


section Define

/-- Define the quadratic character with values in ℤ on a monoid with zero `α`.
It takes the value zero at zero; for non-zero argument `a : α`, it is `1`
if `a` is a square, otherwise it is `-1`.

This only deserves the name "character" when it is multiplicative,
e.g., when `α` is a finite field. See `quadratic_char_mul`.
-/
def quadraticChar (α : Type _) [MonoidWithZeroₓ α] [DecidableEq α] [DecidablePred (IsSquare : α → Prop)] (a : α) : ℤ :=
  if a = 0 then 0 else if IsSquare a then 1 else -1

end Define

/-!
### Basic properties of the quadratic character

We prove some properties of the quadratic character.
We work with a finite field `F` here.
The interesting case is when the characteristic of `F` is odd.
-/


section QuadraticChar

variable {F : Type _} [Field F] [Fintype F] [DecidableEq F]

/-- Some basic API lemmas -/
theorem quadratic_char_eq_zero_iff (a : F) : quadraticChar F a = 0 ↔ a = 0 := by
  simp only [quadratic_char]
  by_cases' ha : a = 0
  · simp only [ha, eq_self_iff_true, if_true]
    
  · simp only [ha, if_false, iff_falseₓ]
    split_ifs <;> simp only [neg_eq_zero, one_ne_zero, not_false_iff]
    

@[simp]
theorem quadratic_char_zero : quadraticChar F 0 = 0 := by
  simp only [quadratic_char, eq_self_iff_true, if_true, id.def]

@[simp]
theorem quadratic_char_one : quadraticChar F 1 = 1 := by
  simp only [quadratic_char, one_ne_zero, is_square_one, if_true, if_false, id.def]

/-- For nonzero `a : F`, `quadratic_char F a = 1 ↔ is_square a`. -/
theorem quadratic_char_one_iff_is_square {a : F} (ha : a ≠ 0) : quadraticChar F a = 1 ↔ IsSquare a := by
  simp only [quadratic_char, ha,
    (by
      decide : (-1 : ℤ) ≠ 1),
    if_false, ite_eq_left_iff]
  tauto

/-- The quadratic character takes the value `1` on nonzero squares. -/
theorem quadratic_char_sq_one' {a : F} (ha : a ≠ 0) : quadraticChar F (a ^ 2) = 1 := by
  simp only [quadratic_char, ha, pow_eq_zero_iff, Nat.succ_pos', is_square_sq, if_true, if_false]

/-- If `ring_char F = 2`, then `quadratic_char F` takes the value `1` on nonzero elements. -/
theorem quadratic_char_eq_one_of_char_two (hF : ringChar F = 2) {a : F} (ha : a ≠ 0) : quadraticChar F a = 1 := by
  simp only [quadratic_char, ha, if_false, ite_eq_left_iff]
  intro h
  exfalso
  exact h (FiniteField.is_square_of_char_two hF a)

/-- If `ring_char F` is odd, then `quadratic_char F a` can be computed in
terms of `a ^ (fintype.card F / 2)`. -/
theorem quadratic_char_eq_pow_of_char_ne_two (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) :
    quadraticChar F a = if a ^ (Fintype.card F / 2) = 1 then 1 else -1 := by
  simp only [quadratic_char, ha, if_false]
  simp_rw [FiniteField.is_square_iff hF ha]

/-- The quadratic character is multiplicative. -/
theorem quadratic_char_mul (a b : F) : quadraticChar F (a * b) = quadraticChar F a * quadraticChar F b := by
  by_cases' ha : a = 0
  · rw [ha, zero_mul, quadratic_char_zero, zero_mul]
    
  -- now `a ≠ 0`
  by_cases' hb : b = 0
  · rw [hb, mul_zero, quadratic_char_zero, mul_zero]
    
  -- now `a ≠ 0` and `b ≠ 0`
  have hab := mul_ne_zero ha hb
  by_cases' hF : ringChar F = 2
  · -- case `ring_char F = 2`
    rw [quadratic_char_eq_one_of_char_two hF ha, quadratic_char_eq_one_of_char_two hF hb,
      quadratic_char_eq_one_of_char_two hF hab, mul_oneₓ]
    
  · -- case of odd characteristic
    rw [quadratic_char_eq_pow_of_char_ne_two hF ha, quadratic_char_eq_pow_of_char_ne_two hF hb,
      quadratic_char_eq_pow_of_char_ne_two hF hab, mul_powₓ]
    cases' FiniteField.pow_dichotomy hF hb with hb' hb'
    · simp only [hb', mul_oneₓ, eq_self_iff_true, if_true]
      
    · have h := FiniteField.neg_one_ne_one_of_char_ne_two hF
      -- `-1 ≠ 1`
      simp only [hb', h, mul_neg, mul_oneₓ, if_false, ite_mul, neg_mul]
      cases' FiniteField.pow_dichotomy hF ha with ha' ha' <;>
        simp only [ha', h, neg_negₓ, eq_self_iff_true, if_true, if_false]
      
    

/-- The quadratic character is a homomorphism of monoids with zero. -/
@[simps]
def quadraticCharHom : F →*₀ ℤ where
  toFun := quadraticChar F
  map_zero' := quadratic_char_zero
  map_one' := quadratic_char_one
  map_mul' := quadratic_char_mul

/-- The square of the quadratic character on nonzero arguments is `1`. -/
theorem quadratic_char_sq_one {a : F} (ha : a ≠ 0) : quadraticChar F a ^ 2 = 1 := by
  rwa [pow_two, ← quadratic_char_mul, ← pow_two, quadratic_char_sq_one']

/-- The quadratic character is `1` or `-1` on nonzero arguments. -/
theorem quadratic_char_dichotomy {a : F} (ha : a ≠ 0) : quadraticChar F a = 1 ∨ quadraticChar F a = -1 :=
  (sq_eq_one_iff (quadraticChar F a)).mp (quadratic_char_sq_one ha)

/-- If `F` has odd characteristic, then `quadratic_char F` takes the value `-1`. -/
theorem quadratic_char_exists_neg_one (hF : ringChar F ≠ 2) : ∃ a, quadraticChar F a = -1 := by
  cases' FiniteField.exists_nonsquare hF with b h₁
  have hb : b ≠ 0 := by
    intro hf
    rw [hf] at h₁
    exact h₁ (is_square_zero F)
  use b
  simp only [quadratic_char, hb, if_false, ite_eq_right_iff]
  tauto

open BigOperators

/-- The sum over the values of the quadratic character is zero when the characteristic is odd. -/
theorem quadratic_char_sum_zero (hF : ringChar F ≠ 2) : (∑ a : F, quadraticChar F a) = 0 := by
  cases' quadratic_char_exists_neg_one hF with b hb
  have h₀ : b ≠ 0 := by
    intro hf
    rw [hf, quadratic_char_zero, zero_eq_neg] at hb
    exact one_ne_zero hb
  let mul_b : F → F := fun x => b * x
  have h₁ : (∑ a : F, quadratic_char F (b * a)) = ∑ a : F, quadratic_char F a := by
    refine' Fintype.sum_bijective _ (mul_left_bijective₀ b h₀) _ _ fun x => rfl
  simp only [quadratic_char_mul] at h₁
  rw [← Finset.mul_sum, hb, neg_mul, one_mulₓ] at h₁
  exact eq_zero_of_neg_eq h₁

end QuadraticChar

end Charₓ

/-!
### Quadratic characters mod 4 and 8

We define the primitive quadratic characters `χ₄`on `zmod 4`
and `χ₈`, `χ₈'` on `zmod 8`.
-/


namespace Zmod

section QuadCharModP

/-- Define the nontrivial quadratic character on `zmod 4`, `χ₄`.
It corresponds to the extension `ℚ(√-1)/ℚ`. -/
@[simps]
def χ₄ : Zmod 4 →*₀ ℤ where
  toFun := (![0, 1, 0, -1] : Zmod 4 → ℤ)
  map_zero' := rfl
  map_one' := rfl
  map_mul' := by
    decide

/-- Define the first primitive quadratic character on `zmod 8`, `χ₈`.
It corresponds to the extension `ℚ(√2)/ℚ`. -/
@[simps]
def χ₈ : Zmod 8 →*₀ ℤ where
  toFun := (![0, 1, 0, -1, 0, -1, 0, 1] : Zmod 8 → ℤ)
  map_zero' := rfl
  map_one' := rfl
  map_mul' := by
    decide

/-- Define the second primitive quadratic character on `zmod 8`, `χ₈'`.
It corresponds to the extension `ℚ(√-2)/ℚ`. -/
@[simps]
def χ₈' : Zmod 8 →*₀ ℤ where
  toFun := (![0, 1, 0, 1, 0, -1, 0, -1] : Zmod 8 → ℤ)
  map_zero' := rfl
  map_one' := rfl
  map_mul' := by
    decide

end QuadCharModP

end Zmod

