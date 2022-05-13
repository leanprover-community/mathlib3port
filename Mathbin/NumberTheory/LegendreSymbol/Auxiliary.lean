/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathbin.Tactic.Basic
import Mathbin.FieldTheory.Finite.Basic

/-!
# Some auxiliary results

We collect some results here that are not specific to quadratic characters
or Legendre symbols, but are needed in some places there.
They will be moved to appropriate places eventually.
-/


section General

/-- A natural number is odd iff it has residue `1` or `3` mod `4`-/
theorem Nat.odd_mod_four_iff {n : ℕ} : n % 2 = 1 ↔ n % 4 = 1 ∨ n % 4 = 3 := by
  constructor
  · have help : ∀ m : ℕ, 0 ≤ m → m < 4 → m % 2 = 1 → m = 1 ∨ m = 3 := by
      decide
    intro hn
    rw [←
      Nat.mod_mod_of_dvd n
        (by
          norm_num : 2 ∣ 4)] at
      hn
    exact
      help (n % 4) zero_le'
        (Nat.mod_ltₓ n
          (by
            norm_num))
        hn
    
  · intro h
    cases' h with h h
    · exact Nat.odd_of_mod_four_eq_one h
      
    · exact Nat.odd_of_mod_four_eq_three h
      
    

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

/-- The finite field `F` has even cardinality iff it has characteristic `2`. -/
theorem even_card_iff_char_two : ringChar F = 2 ↔ Fintype.card F % 2 = 0 := by
  rcases FiniteField.card F (ringChar F) with ⟨n, hp, h⟩
  rw [h, Nat.pow_mod]
  constructor
  · intro hF
    rw [hF]
    simp only [Nat.bit0_mod_two, zero_pow', Ne.def, Pnat.ne_zero, not_false_iff, Nat.zero_modₓ]
    
  · rw [← Nat.even_iff, Nat.even_pow]
    rintro ⟨hev, hnz⟩
    rw [Nat.even_iff, Nat.mod_modₓ] at hev
    cases' Nat.Prime.eq_two_or_odd hp with h₁ h₁
    · exact h₁
      
    · exact False.ndrec (ringChar F = 2) (one_ne_zero ((Eq.symm h₁).trans hev))
      
    

theorem even_card_of_char_two (hF : ringChar F = 2) : Fintype.card F % 2 = 0 :=
  even_card_iff_char_two.mp hF

theorem odd_card_of_char_ne_two (hF : ringChar F ≠ 2) : Fintype.card F % 2 = 1 :=
  Nat.mod_two_ne_zero.mp (mt even_card_iff_char_two.mpr hF)

/-- Characteristic `≠ 2` implies that `-1 ≠ 1`. -/
theorem neg_one_ne_one_of_char_ne_two (hF : ringChar F ≠ 2) : (-1 : F) ≠ 1 := by
  have hc := CharP.char_is_prime F (ringChar F)
  have hF' : Fact (2 < ringChar F) := ⟨lt_of_le_of_neₓ (Nat.Prime.two_le hc) (Ne.symm hF)⟩
  exact CharP.neg_one_ne_one _ (ringChar F)

/-- Characteristic `≠ 2` implies that `-a ≠ a` when `a ≠ 0`. -/
theorem neg_ne_self_of_char_ne_two (hF : ringChar F ≠ 2) {a : F} (ha : a ≠ 0) : a ≠ -a := by
  intro hf
  apply (neg_one_ne_one_of_char_ne_two hF).symm
  rw [eq_neg_iff_add_eq_zero, ← two_mul, mul_oneₓ]
  rw [eq_neg_iff_add_eq_zero, ← two_mul, mul_eq_zero] at hf
  exact hf.resolve_right ha

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

