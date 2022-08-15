/-
Copyright (c) 2022 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
import Mathbin.NumberTheory.LegendreSymbol.AddCharacter
import Mathbin.NumberTheory.LegendreSymbol.ZmodChar
import Mathbin.Algebra.CharP.CharAndCard

/-!
# Gauss sums

We define the Gauss sum associated to a multiplicative and an additive
character of a finite field and prove some results about them.

## Main definition

Let `R` be a finite commutative ring and let `R'` be another commutative ring.
If `χ` is a multiplicative character `R → R'` (type `mul_char R R'`) and `ψ`
is an additive character `R → R'` (type `add_char R R'`, which abbreviates
`(multiplicative R) →* R'`), then the *Gauss sum* of `χ` and `ψ` is `∑ a, χ a * ψ a`.

## Main results

Some important results are as follows.

* `gauss_sum_mul_gauss_sum_eq_card`: The product of the Gauss
  sums of `χ` and `ψ` and that of `χ⁻¹` and `ψ⁻¹` is the cardinality
  of the source ring `R` (if `χ` is nontrivial, `ψ` is primitive and `R` is a field).
* `gauss_sum_sq`: The square of the Gauss sum is `χ(-1)` times
  the cardinality of `R` if in addition `χ` is a quadratic character.
* `quad_gauss_sum_frob`: For a quadratic character `χ`, raising
  the Gauss sum to the `p`th power (where `p` is the characteristic of
  the target ring `R'`) multiplies it by `χ p`.
* `char.card_pow_card`: When `F` and `F'` are finite fields and `χ : F → F'`
  is a nontrivial quadratic character, then `(χ (-1) * #F)^(#F'/2) = χ (#F')`.
* `finite_field.two_pow_card`: For every finite field `F` of odd characteristic,
  we have `2^(#F/2) = χ₈(#F)` in `F`.

This machinery can be used to derive (a generalization of) the Law of
Quadratic Reciprocity.

## Tags

additive character, multiplicative character, Gauss sum
-/


universe u v

open BigOperators

open AddChar MulChar Multiplicative

section GaussSumDef

-- `R` is the domain of the characters
variable {R : Type u} [CommRingₓ R] [Fintype R]

-- `R'` is the target of the characters
variable {R' : Type v} [CommRingₓ R']

/-!
### Definition and first properties
-/


/-- Definition of the Gauss sum associated to a multiplicative and an additive character. -/
def gaussSum (χ : MulChar R R') (ψ : AddChar R R') : R' :=
  ∑ a, χ a * ψ (ofAdd a)

/-- Replacing `ψ` by `mul_shift ψ a` and multiplying the Gauss sum by `χ a` does not change it. -/
theorem gauss_sum_mul_shift (χ : MulChar R R') (ψ : AddChar R R') (a : Rˣ) :
    χ a * gaussSum χ (mulShift ψ a) = gaussSum χ ψ := by
  simp only [← gaussSum, ← mul_shift, ← MonoidHom.coe_comp, ← Function.comp_app, ← to_add_of_add, ←
    AddMonoidHom.to_multiplicative_apply_apply, ← AddMonoidHom.coe_mul_left]
  rw [Finset.mul_sum]
  simp_rw [← mul_assoc, ← map_mul]
  exact Fintype.sum_bijective _ a.mul_left_bijective _ _ fun x => rfl

end GaussSumDef

/-!
### The product of two Gauss sums
-/


section GaussSumProd

-- In the following, we need `R` to be a finite field and `R'` to be a domain.
variable {R : Type u} [Field R] [Fintype R] {R' : Type v} [CommRingₓ R'] [IsDomain R']

-- A helper lemma for `gauss_sum_mul_gauss_sum_eq_card` below
-- Is this useful enough in other contexts to be public?
private theorem gauss_sum_mul_aux {χ : MulChar R R'} (hχ : IsNontrivial χ) (ψ : AddChar R R') (b : R) :
    (∑ a, χ (a * b⁻¹) * ψ (ofAdd (a - b))) = ∑ c, χ c * ψ (of_add <| b * (c - 1)) := by
  cases' eq_or_ne b 0 with hb hb
  · -- case `b = 0`
    simp only [← hb, ← inv_zero, ← mul_zero, ← MulChar.map_zero, ← zero_mul, ← Finset.sum_const_zero, ← of_add_zero, ←
      MonoidHom.map_one, ← mul_oneₓ]
    exact hχ.sum_eq_zero.symm
    
  · -- case `b ≠ 0`
    refine' ((Fintype.sum_bijective _ (mul_left_bijective₀ b hb) _ _) fun x => _).symm
    rw [mul_assoc, mul_comm x, ← mul_assoc, mul_inv_cancel hb, one_mulₓ, mul_sub, mul_oneₓ]
    

-- ./././Mathport/Syntax/Translate/Basic.lean:855:6: warning: expanding binder group (y x)
/-- We have `gauss_sum χ ψ * gauss_sum χ⁻¹ ψ⁻¹ = fintype.card R`
when `χ` is nontrivial and `ψ` is primitive (and `R` is a field). -/
theorem gauss_sum_mul_gauss_sum_eq_card {χ : MulChar R R'} (hχ : IsNontrivial χ) {ψ : AddChar R R'}
    (hψ : IsPrimitive ψ) : gaussSum χ ψ * gaussSum χ⁻¹ ψ⁻¹ = Fintype.card R := by
  simp only [← gaussSum, ← inv_mul_shift, ← mul_shift, ← MonoidHom.coe_comp, ← Function.comp_app, ←
    AddMonoidHom.to_multiplicative_apply_apply, ← Finset.mul_sum, ← AddMonoidHom.coe_mul_left, ← neg_mul, ← one_mulₓ, ←
    of_add_neg, ← of_add_to_add]
  simp_rw [Finset.sum_mul, mul_mul_mul_commₓ, inv_apply' χ, ← map_mul χ, ← map_mul ψ]
  convert_to (∑ (y) (x), χ (x * y⁻¹) * ψ (of_add (x - y))) = _
  · simp_rw [sub_eq_add_neg]
    rfl
    
  simp_rw [gauss_sum_mul_aux hχ ψ]
  rw [Finset.sum_comm]
  classical
  -- to get `[decidable_eq R]` for `gauss_sum_mul_aux₂`
  simp_rw [← Finset.mul_sum, sum_mul_shift _ _ hψ, sub_eq_zero, mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (1 : R)]
  simp only [← Finset.mem_univ, ← map_one, ← one_mulₓ, ← if_true]

/-- When `χ` is a nontrivial quadratic character, then the square of `gauss_sum χ ψ`
is `χ(-1)` times the cardinality of `R`. -/
theorem gauss_sum_sq {χ : MulChar R R'} (hχ₁ : IsNontrivial χ) (hχ₂ : IsQuadratic χ) {ψ : AddChar R R'}
    (hψ : IsPrimitive ψ) : gaussSum χ ψ ^ 2 = χ (-1) * Fintype.card R := by
  rw [pow_two, ← gauss_sum_mul_gauss_sum_eq_card hχ₁ hψ, hχ₂.inv, mul_rotate']
  congr
  rw [mul_comm, ← gauss_sum_mul_shift _ _ (-1 : Rˣ), inv_mul_shift]
  rfl

end GaussSumProd

/-!
### Gauss sums and Frobenius
-/


section gauss_sum_frob

variable {R : Type u} [CommRingₓ R] [Fintype R] {R' : Type v} [CommRingₓ R']

-- We assume that the target ring `R'` has prime characteristic `p`.
variable (p : ℕ) [fp : Fact p.Prime] [hch : CharP R' p]

include fp hch

/-- When `R'` has prime characteristic `p`, then the `p`th power of the Gauss sum
of `χ` and `ψ` is the Gauss sum of `χ^p` and `mul_shift ψ p`. -/
theorem gauss_sum_frob (χ : MulChar R R') (ψ : AddChar R R') : gaussSum χ ψ ^ p = gaussSum (χ ^ p) (ψ ^ p) := by
  rw [← frobenius_def, gaussSum, gaussSum, map_sum]
  simp_rw [pow_apply' χ fp.1.Pos, map_mul, frobenius_def]
  rfl

/-- For a quadratic character `χ` and when the characteristic `p` of the target ring
is a unit in the source ring, the `p`th power of the Gauss sum of`χ` and `ψ` is
`χ p` times the original Gauss sum. -/
theorem MulChar.IsQuadratic.gauss_sum_frob (hp : IsUnit (p : R)) {χ : MulChar R R'} (hχ : IsQuadratic χ)
    (ψ : AddChar R R') : gaussSum χ ψ ^ p = χ p * gaussSum χ ψ := by
  rw [gauss_sum_frob, pow_mul_shift, hχ.pow_char p, ← gauss_sum_mul_shift χ ψ hp.unit, ← mul_assoc, hp.unit_spec, ←
    pow_two, ←
    pow_apply' _
      (by
        norm_num : 0 < 2),
    hχ.sq_eq_one, ← hp.unit_spec, one_apply_coe, one_mulₓ]

/-- For a quadratic character `χ` and when the characteristic `p` of the target ring
is a unit in the source ring and `n` is a natural number, the `p^n`th power of the Gauss
sum of`χ` and `ψ` is `χ (p^n)` times the original Gauss sum. -/
theorem MulChar.IsQuadratic.gauss_sum_frob_iter (n : ℕ) (hp : IsUnit (p : R)) {χ : MulChar R R'} (hχ : IsQuadratic χ)
    (ψ : AddChar R R') : gaussSum χ ψ ^ p ^ n = χ (p ^ n) * gaussSum χ ψ := by
  induction' n with n ih
  · rw [pow_zeroₓ, pow_oneₓ, pow_zeroₓ, MulChar.map_one, one_mulₓ]
    
  · rw [pow_succₓ, mul_comm p, pow_mulₓ, ih, mul_powₓ, hχ.gauss_sum_frob _ hp, ← mul_assoc, pow_succₓ, mul_comm (p : R),
      map_mul, ← pow_apply' χ fp.1.Pos (p ^ n), hχ.pow_char p]
    

end gauss_sum_frob

/-!
### Values of quadratic characters
-/


section GaussSumValues

variable {R : Type u} [CommRingₓ R] [Fintype R] {R' : Type v} [CommRingₓ R'] [IsDomain R']

/-- If the square of the Gauss sum of a quadratic character is `χ(-1) * #R`,
then we get, for all `n : ℕ`, the relation `(χ(-1) * #R) ^ (p^n/2) = χ(p^n)`,
where `p` is the (odd) characteristic of the target ring `R'`.
This version can be used when `R` is not a field, e.g., `ℤ/8ℤ`. -/
theorem Charₓ.card_pow_char_pow {χ : MulChar R R'} (hχ : IsQuadratic χ) (ψ : AddChar R R') (p n : ℕ) [fp : Fact p.Prime]
    [hch : CharP R' p] (hp : IsUnit (p : R)) (hp' : p ≠ 2) (hg : gaussSum χ ψ ^ 2 = χ (-1) * Fintype.card R) :
    (χ (-1) * Fintype.card R) ^ (p ^ n / 2) = χ (p ^ n) := by
  have : gaussSum χ ψ ≠ 0 := by
    intro hf
    rw [hf,
      zero_pow
        (by
          norm_num : 0 < 2),
      eq_comm, mul_eq_zero] at hg
    exact
      not_is_unit_prime_of_dvd_card p
        ((CharP.cast_eq_zero_iff R' p _).mp <| hg.resolve_left (is_unit_one.neg.map χ).ne_zero) hp
  rw [← hg]
  apply mul_right_cancel₀ this
  rw [← hχ.gauss_sum_frob_iter p n hp ψ, ← pow_mulₓ, mul_comm, ← pow_succₓ,
    Nat.two_mul_div_two_add_one_of_odd (fp.1.eq_two_or_odd'.resolve_left hp').pow]

/-- When `F` and `F'` are finite fields and `χ : F → F'` is a nontrivial quadratic character,
then `(χ(-1) * #F)^(#F'/2) = χ(#F')`. -/
theorem Charₓ.card_pow_card {F : Type} [Field F] [Fintype F] {F' : Type} [Field F'] [Fintype F'] {χ : MulChar F F'}
    (hχ₁ : IsNontrivial χ) (hχ₂ : IsQuadratic χ) (hch₁ : ringChar F' ≠ ringChar F) (hch₂ : ringChar F' ≠ 2) :
    (χ (-1) * Fintype.card F) ^ (Fintype.card F' / 2) = χ (Fintype.card F') := by
  obtain ⟨n, hp, hc⟩ := FiniteField.card F (ringChar F)
  obtain ⟨n', hp', hc'⟩ := FiniteField.card F' (ringChar F')
  let ψ := primitive_char_finite_field F F' hch₁
  let FF' := CyclotomicField ψ.n F'
  have hchar := Algebra.ring_char_eq F' FF'
  apply (algebraMap F' FF').Injective
  rw [map_pow, map_mul, map_nat_cast, hc', hchar, Nat.cast_powₓ]
  simp only [MulChar.ring_hom_comp_apply]
  haveI := Fact.mk hp'
  haveI := Fact.mk (hchar.subst hp')
  rw [Ne, ← Nat.prime_dvd_prime_iff_eq hp' hp, ← is_unit_iff_not_dvd_char, hchar] at hch₁
  exact
    Charₓ.card_pow_char_pow (hχ₂.comp _) ψ.char (ringChar FF') n' hch₁ (hchar ▸ hch₂)
      (gauss_sum_sq (hχ₁.comp <| RingHom.injective _) (hχ₂.comp _) ψ.prim)

end GaussSumValues

section GaussSumTwo

/-!
### The quadratic character of 2

This section proves the following result.

For every finite field `F` of odd characteristic, we have `2^(#F/2) = χ₈(#F)` in `F`.
This can be used to show that the quadratic character of `F` takes the value
`χ₈(#F)` at `2`.

The proof uses the Gauss sum of `χ₈` and a primitive additive character on `ℤ/8ℤ`;
in this way, the result is reduced to `card_pow_char_pow`.
-/


open Zmod

/-- For every finite field `F` of odd characteristic, we have `2^(#F/2) = χ₈(#F)` in `F`. -/
theorem FiniteField.two_pow_card {F : Type _} [Fintype F] [Field F] (hF : ringChar F ≠ 2) :
    (2 : F) ^ (Fintype.card F / 2) = χ₈ (Fintype.card F) := by
  have hp2 : ∀ n : ℕ, (2 ^ n : F) ≠ 0 := fun n => pow_ne_zero n (Ringₓ.two_ne_zero hF)
  obtain ⟨n, hp, hc⟩ := FiniteField.card F (ringChar F)
  -- we work in `FF`, the eighth cyclotomic field extension of `F`
  let FF := (Polynomial.cyclotomic 8 F).SplittingField
  haveI : FiniteDimensional F FF := Polynomial.IsSplittingField.finite_dimensional FF (Polynomial.cyclotomic 8 F)
  haveI : Fintype FF := FiniteDimensional.fintypeOfFintype F FF
  have hchar := Algebra.ring_char_eq F FF
  have FFp := hchar.subst hp
  haveI := Fact.mk FFp
  have hFF := ne_of_eq_of_ne hchar.symm hF
  -- `ring_char FF ≠ 2`
  have hu : IsUnit (ringChar FF : Zmod 8) := by
    rw [is_unit_iff_not_dvd_char, ring_char_zmod_n]
    rw [Ne, ← Nat.prime_dvd_prime_iff_eq FFp Nat.prime_two] at hFF
    change ¬_ ∣ 2 ^ 3
    exact mt FFp.dvd_of_dvd_pow hFF
  -- there is a primitive additive character `ℤ/8ℤ → FF`, sending `a + 8ℤ ↦ τ^a`
  -- with a primitive eighth root of unity `τ`
  let ψ₈ :=
    primitive_zmod_char 8 F
      (by
        convert hp2 3 <;> norm_num)
  let τ : FF := ψ₈.char (of_add 1)
  have τ_spec : τ ^ 4 = -1 := by
    refine' (sq_eq_one_iff.1 _).resolve_left _ <;>
      · simp only [← τ, map_pow]
        erw [AddChar.IsPrimitive.zmod_char_eq_one_iff 8 ψ₈.prim]
        decide
        
  -- we consider `χ₈` as a multiplicative character `ℤ/8ℤ → FF`
  let χ := χ₈.ring_hom_comp (Int.castRingHom FF)
  have hχ : χ (-1) = 1 := NormNum.int_cast_one
  have hq : is_quadratic χ := is_quadratic_χ₈.comp _
  -- we now show that the Gauss sum of `χ` and `ψ₈` has the relevant property
  have hg : gaussSum χ ψ₈.char ^ 2 = χ (-1) * Fintype.card (Zmod 8) := by
    rw [hχ, one_mulₓ, card, gaussSum]
    convert ← congr_arg (· ^ 2) (Finₓ.sum_univ_eight fun x => (χ₈ x : FF) * τ ^ x.val)
    · ext
      congr
      apply pow_oneₓ
      
    convert_to (0 + 1 * τ ^ 1 + 0 + -1 * τ ^ 3 + 0 + -1 * τ ^ 5 + 0 + 1 * τ ^ 7) ^ 2 = _
    · simp only [← χ₈_apply, ← Matrix.cons_val_zero, ← Matrix.cons_val_one, ← Matrix.head_cons, ←
        Matrix.cons_vec_bit0_eq_alt0, ← Matrix.cons_vec_bit1_eq_alt1, ← Matrix.cons_append, ← Matrix.cons_vec_alt0, ←
        Matrix.cons_vec_alt1, ← Int.cast_zeroₓ, ← Int.cast_oneₓ, ← Int.cast_neg, ← zero_mul]
      rfl
      
    convert_to 8 + (τ ^ 4 + 1) * (τ ^ 10 - 2 * τ ^ 8 - 2 * τ ^ 6 + 6 * τ ^ 4 + τ ^ 2 - 8) = _
    · ring
      
    · rw [τ_spec]
      norm_num
      
  -- this allows us to apply `card_pow_char_pow` to our situation
  have h := Charₓ.card_pow_char_pow hq ψ₈.char (ringChar FF) n hu hFF hg
  rw [card, ← hchar, hχ, one_mulₓ, ← hc, ← Nat.cast_powₓ (ringChar F), ← hc] at h
  -- finally, we change `2` to `8` on the left hand side
  convert_to (8 : F) ^ (Fintype.card F / 2) = _
  · rw
      [(by
        norm_num : (8 : F) = 2 ^ 2 * 2),
      mul_powₓ, (FiniteField.is_square_iff hF <| hp2 2).mp ⟨2, pow_two 2⟩, one_mulₓ]
    
  apply (algebraMap F FF).Injective
  simp only [← map_pow, ← map_bit0, ← map_one, ← RingHom.map_int_cast]
  convert h
  norm_num

end GaussSumTwo

