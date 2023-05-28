/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen

! This file was ported from Lean 3 source module ring_theory.localization.integral
! leanprover-community/mathlib commit 61db041ab8e4aaf8cb5c7dc10a7d4ff261997536
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.Data.Polynomial.Lifts
import Mathbin.GroupTheory.MonoidLocalization
import Mathbin.RingTheory.Algebraic
import Mathbin.RingTheory.Ideal.LocalRing
import Mathbin.RingTheory.IntegralClosure
import Mathbin.RingTheory.Localization.FractionRing
import Mathbin.RingTheory.Localization.Integer
import Mathbin.RingTheory.NonZeroDivisors
import Mathbin.Tactic.RingExp

/-!
# Integral and algebraic elements of a fraction field

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Implementation notes

See `src/ring_theory/localization/basic.lean` for a design overview.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions
-/


variable {R : Type _} [CommRing R] (M : Submonoid R) {S : Type _} [CommRing S]

variable [Algebra R S] {P : Type _} [CommRing P]

open BigOperators Polynomial

namespace IsLocalization

section IntegerNormalization

open Polynomial

variable (M) {S} [IsLocalization M S]

open Classical

#print IsLocalization.coeffIntegerNormalization /-
/-- `coeff_integer_normalization p` gives the coefficients of the polynomial
`integer_normalization p` -/
noncomputable def coeffIntegerNormalization (p : S[X]) (i : ℕ) : R :=
  if hi : i ∈ p.support then
    Classical.choose
      (Classical.choose_spec (exist_integer_multiples_of_finset M (p.support.image p.coeff))
        (p.coeff i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩))
  else 0
#align is_localization.coeff_integer_normalization IsLocalization.coeffIntegerNormalization
-/

/- warning: is_localization.coeff_integer_normalization_of_not_mem_support -> IsLocalization.coeffIntegerNormalization_of_not_mem_support is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) {S : Type.{u2}} [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))] [_inst_5 : IsLocalization.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M S (CommRing.toCommSemiring.{u2} S _inst_2) _inst_3] (p : Polynomial.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))) (i : Nat), (Eq.{succ u2} S (Polynomial.coeff.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)) p i) (OfNat.ofNat.{u2} S 0 (OfNat.mk.{u2} S 0 (Zero.zero.{u2} S (MulZeroClass.toHasZero.{u2} S (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} S (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} S (NonAssocRing.toNonUnitalNonAssocRing.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2)))))))))) -> (Eq.{succ u1} R (IsLocalization.coeffIntegerNormalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5 p i) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) {S : Type.{u2}} [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2))] [_inst_5 : IsLocalization.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M S (CommRing.toCommSemiring.{u2} S _inst_2) _inst_3] (p : Polynomial.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2))) (i : Nat), (Eq.{succ u2} S (Polynomial.coeff.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)) p i) (OfNat.ofNat.{u2} S 0 (Zero.toOfNat0.{u2} S (CommMonoidWithZero.toZero.{u2} S (CommSemiring.toCommMonoidWithZero.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)))))) -> (Eq.{succ u1} R (IsLocalization.coeffIntegerNormalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5 p i) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))))))
Case conversion may be inaccurate. Consider using '#align is_localization.coeff_integer_normalization_of_not_mem_support IsLocalization.coeffIntegerNormalization_of_not_mem_supportₓ'. -/
theorem coeffIntegerNormalization_of_not_mem_support (p : S[X]) (i : ℕ) (h : coeff p i = 0) :
    coeffIntegerNormalization M p i = 0 := by
  simp only [coeff_integer_normalization, h, mem_support_iff, eq_self_iff_true, not_true, Ne.def,
    dif_neg, not_false_iff]
#align is_localization.coeff_integer_normalization_of_not_mem_support IsLocalization.coeffIntegerNormalization_of_not_mem_support

/- warning: is_localization.coeff_integer_normalization_mem_support -> IsLocalization.coeffIntegerNormalization_mem_support is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) {S : Type.{u2}} [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))] [_inst_5 : IsLocalization.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M S (CommRing.toCommSemiring.{u2} S _inst_2) _inst_3] (p : Polynomial.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))) (i : Nat), (Ne.{succ u1} R (IsLocalization.coeffIntegerNormalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5 p i) (OfNat.ofNat.{u1} R 0 (OfNat.mk.{u1} R 0 (Zero.zero.{u1} R (MulZeroClass.toHasZero.{u1} R (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} R (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} R (NonAssocRing.toNonUnitalNonAssocRing.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))))))) -> (Membership.Mem.{0, 0} Nat (Finset.{0} Nat) (Finset.hasMem.{0} Nat) i (Polynomial.support.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)) p))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) {S : Type.{u2}} [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2))] [_inst_5 : IsLocalization.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M S (CommRing.toCommSemiring.{u2} S _inst_2) _inst_3] (p : Polynomial.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2))) (i : Nat), (Ne.{succ u1} R (IsLocalization.coeffIntegerNormalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5 p i) (OfNat.ofNat.{u1} R 0 (Zero.toOfNat0.{u1} R (CommMonoidWithZero.toZero.{u1} R (CommSemiring.toCommMonoidWithZero.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) -> (Membership.mem.{0, 0} Nat (Finset.{0} Nat) (Finset.instMembershipFinset.{0} Nat) i (Polynomial.support.{u2} S (CommSemiring.toSemiring.{u2} S (CommRing.toCommSemiring.{u2} S _inst_2)) p))
Case conversion may be inaccurate. Consider using '#align is_localization.coeff_integer_normalization_mem_support IsLocalization.coeffIntegerNormalization_mem_supportₓ'. -/
theorem coeffIntegerNormalization_mem_support (p : S[X]) (i : ℕ)
    (h : coeffIntegerNormalization M p i ≠ 0) : i ∈ p.support :=
  by
  contrapose h
  rw [Ne.def, Classical.not_not, coeff_integer_normalization, dif_neg h]
#align is_localization.coeff_integer_normalization_mem_support IsLocalization.coeffIntegerNormalization_mem_support

#print IsLocalization.integerNormalization /-
/-- `integer_normalization g` normalizes `g` to have integer coefficients
by clearing the denominators -/
noncomputable def integerNormalization (p : S[X]) : R[X] :=
  ∑ i in p.support, monomial i (coeffIntegerNormalization M p i)
#align is_localization.integer_normalization IsLocalization.integerNormalization
-/

#print IsLocalization.integerNormalization_coeff /-
@[simp]
theorem integerNormalization_coeff (p : S[X]) (i : ℕ) :
    (integerNormalization M p).coeff i = coeffIntegerNormalization M p i := by
  simp (config := { contextual := true }) [integer_normalization, coeff_monomial,
    coeff_integer_normalization_of_not_mem_support]
#align is_localization.integer_normalization_coeff IsLocalization.integerNormalization_coeff
-/

/- warning: is_localization.integer_normalization_spec -> IsLocalization.integerNormalization_spec is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.integer_normalization_spec IsLocalization.integerNormalization_specₓ'. -/
theorem integerNormalization_spec (p : S[X]) :
    ∃ b : M, ∀ i, algebraMap R S ((integerNormalization M p).coeff i) = (b : R) • p.coeff i :=
  by
  use Classical.choose (exist_integer_multiples_of_finset M (p.support.image p.coeff))
  intro i
  rw [integer_normalization_coeff, coeff_integer_normalization]
  split_ifs with hi
  ·
    exact
      Classical.choose_spec
        (Classical.choose_spec (exist_integer_multiples_of_finset M (p.support.image p.coeff))
          (p.coeff i) (finset.mem_image.mpr ⟨i, hi, rfl⟩))
  · convert(smul_zero _).symm
    · apply RingHom.map_zero
    · exact not_mem_support_iff.mp hi
#align is_localization.integer_normalization_spec IsLocalization.integerNormalization_spec

/- warning: is_localization.integer_normalization_map_to_map -> IsLocalization.integerNormalization_map_to_map is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.integer_normalization_map_to_map IsLocalization.integerNormalization_map_to_mapₓ'. -/
theorem integerNormalization_map_to_map (p : S[X]) :
    ∃ b : M, (integerNormalization M p).map (algebraMap R S) = (b : R) • p :=
  let ⟨b, hb⟩ := integerNormalization_spec M p
  ⟨b,
    Polynomial.ext fun i => by
      rw [coeff_map, coeff_smul]
      exact hb i⟩
#align is_localization.integer_normalization_map_to_map IsLocalization.integerNormalization_map_to_map

variable {R' : Type _} [CommRing R']

/- warning: is_localization.integer_normalization_eval₂_eq_zero -> IsLocalization.integerNormalization_eval₂_eq_zero is a dubious translation:
lean 3 declaration is
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (NonAssocRing.toNonAssocSemiring.{u1} R (Ring.toNonAssocRing.{u1} R (CommRing.toRing.{u1} R _inst_1)))))) {S : Type.{u2}} [_inst_2 : CommRing.{u2} S] [_inst_3 : Algebra.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))] [_inst_5 : IsLocalization.{u1, u2} R (CommRing.toCommSemiring.{u1} R _inst_1) M S (CommRing.toCommSemiring.{u2} S _inst_2) _inst_3] {R' : Type.{u3}} [_inst_6 : CommRing.{u3} R'] (g : RingHom.{u2, u3} S R' (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2))) (NonAssocRing.toNonAssocSemiring.{u3} R' (Ring.toNonAssocRing.{u3} R' (CommRing.toRing.{u3} R' _inst_6)))) (p : Polynomial.{u2} S (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2))) {x : R'}, (Eq.{succ u3} R' (Polynomial.eval₂.{u2, u3} S R' (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)) (Ring.toSemiring.{u3} R' (CommRing.toRing.{u3} R' _inst_6)) g x p) (OfNat.ofNat.{u3} R' 0 (OfNat.mk.{u3} R' 0 (Zero.zero.{u3} R' (MulZeroClass.toHasZero.{u3} R' (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} R' (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} R' (NonAssocRing.toNonUnitalNonAssocRing.{u3} R' (Ring.toNonAssocRing.{u3} R' (CommRing.toRing.{u3} R' _inst_6)))))))))) -> (Eq.{succ u3} R' (Polynomial.eval₂.{u1, u3} R R' (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (Ring.toSemiring.{u3} R' (CommRing.toRing.{u3} R' _inst_6)) (RingHom.comp.{u1, u2, u3} R S R' (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (NonAssocRing.toNonAssocSemiring.{u2} S (Ring.toNonAssocRing.{u2} S (CommRing.toRing.{u2} S _inst_2))) (NonAssocRing.toNonAssocSemiring.{u3} R' (Ring.toNonAssocRing.{u3} R' (CommRing.toRing.{u3} R' _inst_6))) g (algebraMap.{u1, u2} R S (CommRing.toCommSemiring.{u1} R _inst_1) (Ring.toSemiring.{u2} S (CommRing.toRing.{u2} S _inst_2)) _inst_3)) x (IsLocalization.integerNormalization.{u1, u2} R _inst_1 M S _inst_2 _inst_3 _inst_5 p)) (OfNat.ofNat.{u3} R' 0 (OfNat.mk.{u3} R' 0 (Zero.zero.{u3} R' (MulZeroClass.toHasZero.{u3} R' (NonUnitalNonAssocSemiring.toMulZeroClass.{u3} R' (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u3} R' (NonAssocRing.toNonUnitalNonAssocRing.{u3} R' (Ring.toNonAssocRing.{u3} R' (CommRing.toRing.{u3} R' _inst_6))))))))))
but is expected to have type
  forall {R : Type.{u1}} [_inst_1 : CommRing.{u1} R] (M : Submonoid.{u1} R (MulZeroOneClass.toMulOneClass.{u1} R (NonAssocSemiring.toMulZeroOneClass.{u1} R (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)))))) {S : Type.{u3}} [_inst_2 : CommRing.{u3} S] [_inst_3 : Algebra.{u1, u3} R S (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u3} S (CommRing.toCommSemiring.{u3} S _inst_2))] [_inst_5 : IsLocalization.{u1, u3} R (CommRing.toCommSemiring.{u1} R _inst_1) M S (CommRing.toCommSemiring.{u3} S _inst_2) _inst_3] {R' : Type.{u2}} [_inst_6 : CommRing.{u2} R'] (g : RingHom.{u3, u2} S R' (Semiring.toNonAssocSemiring.{u3} S (CommSemiring.toSemiring.{u3} S (CommRing.toCommSemiring.{u3} S _inst_2))) (Semiring.toNonAssocSemiring.{u2} R' (CommSemiring.toSemiring.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_6)))) (p : Polynomial.{u3} S (CommSemiring.toSemiring.{u3} S (CommRing.toCommSemiring.{u3} S _inst_2))) {x : R'}, (Eq.{succ u2} R' (Polynomial.eval₂.{u3, u2} S R' (CommSemiring.toSemiring.{u3} S (CommRing.toCommSemiring.{u3} S _inst_2)) (CommSemiring.toSemiring.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_6)) g x p) (OfNat.ofNat.{u2} R' 0 (Zero.toOfNat0.{u2} R' (CommMonoidWithZero.toZero.{u2} R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_6)))))) -> (Eq.{succ u2} R' (Polynomial.eval₂.{u1, u2} R R' (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1)) (CommSemiring.toSemiring.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_6)) (RingHom.comp.{u1, u3, u2} R S R' (Semiring.toNonAssocSemiring.{u1} R (CommSemiring.toSemiring.{u1} R (CommRing.toCommSemiring.{u1} R _inst_1))) (Semiring.toNonAssocSemiring.{u3} S (CommSemiring.toSemiring.{u3} S (CommRing.toCommSemiring.{u3} S _inst_2))) (Semiring.toNonAssocSemiring.{u2} R' (CommSemiring.toSemiring.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_6))) g (algebraMap.{u1, u3} R S (CommRing.toCommSemiring.{u1} R _inst_1) (CommSemiring.toSemiring.{u3} S (CommRing.toCommSemiring.{u3} S _inst_2)) _inst_3)) x (IsLocalization.integerNormalization.{u1, u3} R _inst_1 M S _inst_2 _inst_3 _inst_5 p)) (OfNat.ofNat.{u2} R' 0 (Zero.toOfNat0.{u2} R' (CommMonoidWithZero.toZero.{u2} R' (CommSemiring.toCommMonoidWithZero.{u2} R' (CommRing.toCommSemiring.{u2} R' _inst_6))))))
Case conversion may be inaccurate. Consider using '#align is_localization.integer_normalization_eval₂_eq_zero IsLocalization.integerNormalization_eval₂_eq_zeroₓ'. -/
theorem integerNormalization_eval₂_eq_zero (g : S →+* R') (p : S[X]) {x : R'}
    (hx : eval₂ g x p = 0) : eval₂ (g.comp (algebraMap R S)) x (integerNormalization M p) = 0 :=
  let ⟨b, hb⟩ := integerNormalization_map_to_map M p
  trans (eval₂_map (algebraMap R S) g x).symm
    (by rw [hb, ← IsScalarTower.algebraMap_smul S (b : R) p, eval₂_smul, hx, MulZeroClass.mul_zero])
#align is_localization.integer_normalization_eval₂_eq_zero IsLocalization.integerNormalization_eval₂_eq_zero

/- warning: is_localization.integer_normalization_aeval_eq_zero -> IsLocalization.integerNormalization_aeval_eq_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.integer_normalization_aeval_eq_zero IsLocalization.integerNormalization_aeval_eq_zeroₓ'. -/
theorem integerNormalization_aeval_eq_zero [Algebra R R'] [Algebra S R'] [IsScalarTower R S R']
    (p : S[X]) {x : R'} (hx : aeval x p = 0) : aeval x (integerNormalization M p) = 0 := by
  rw [aeval_def, IsScalarTower.algebraMap_eq R S R', integer_normalization_eval₂_eq_zero _ _ _ hx]
#align is_localization.integer_normalization_aeval_eq_zero IsLocalization.integerNormalization_aeval_eq_zero

end IntegerNormalization

end IsLocalization

namespace IsFractionRing

open IsLocalization

variable {A K C : Type _} [CommRing A] [IsDomain A] [Field K] [Algebra A K] [IsFractionRing A K]

variable [CommRing C]

#print IsFractionRing.integerNormalization_eq_zero_iff /-
theorem integerNormalization_eq_zero_iff {p : K[X]} :
    integerNormalization (nonZeroDivisors A) p = 0 ↔ p = 0 :=
  by
  refine' polynomial.ext_iff.trans (polynomial.ext_iff.trans _).symm
  obtain ⟨⟨b, nonzero⟩, hb⟩ := integer_normalization_spec _ p
  constructor <;> intro h i
  · apply to_map_eq_zero_iff.mp
    rw [hb i, h i]
    apply smul_zero
    assumption
  · have hi := h i
    rw [Polynomial.coeff_zero, ← @to_map_eq_zero_iff A _ K, hb i, Algebra.smul_def] at hi
    apply Or.resolve_left (eq_zero_or_eq_zero_of_mul_eq_zero hi)
    intro h
    apply mem_non_zero_divisors_iff_ne_zero.mp nonzero
    exact to_map_eq_zero_iff.mp h
#align is_fraction_ring.integer_normalization_eq_zero_iff IsFractionRing.integerNormalization_eq_zero_iff
-/

variable (A K C)

/- warning: is_fraction_ring.is_algebraic_iff -> IsFractionRing.isAlgebraic_iff is a dubious translation:
lean 3 declaration is
  forall (A : Type.{u1}) (K : Type.{u2}) (C : Type.{u3}) [_inst_5 : CommRing.{u1} A] [_inst_6 : IsDomain.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_5))] [_inst_7 : Field.{u2} K] [_inst_8 : Algebra.{u1, u2} A K (CommRing.toCommSemiring.{u1} A _inst_5) (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_7)))] [_inst_9 : IsFractionRing.{u1, u2} A _inst_5 K (EuclideanDomain.toCommRing.{u2} K (Field.toEuclideanDomain.{u2} K _inst_7)) _inst_8] [_inst_10 : CommRing.{u3} C] [_inst_11 : Algebra.{u1, u3} A C (CommRing.toCommSemiring.{u1} A _inst_5) (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10))] [_inst_12 : Algebra.{u2, u3} K C (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_7)) (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10))] [_inst_13 : IsScalarTower.{u1, u2, u3} A K C (SMulZeroClass.toHasSmul.{u1, u2} A K (AddZeroClass.toHasZero.{u2} K (AddMonoid.toAddZeroClass.{u2} K (AddCommMonoid.toAddMonoid.{u2} K (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_7))))))))) (SMulWithZero.toSmulZeroClass.{u1, u2} A K (MulZeroClass.toHasZero.{u1} A (MulZeroOneClass.toMulZeroClass.{u1} A (MonoidWithZero.toMulZeroOneClass.{u1} A (Semiring.toMonoidWithZero.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_5)))))) (AddZeroClass.toHasZero.{u2} K (AddMonoid.toAddZeroClass.{u2} K (AddCommMonoid.toAddMonoid.{u2} K (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_7))))))))) (MulActionWithZero.toSMulWithZero.{u1, u2} A K (Semiring.toMonoidWithZero.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_5))) (AddZeroClass.toHasZero.{u2} K (AddMonoid.toAddZeroClass.{u2} K (AddCommMonoid.toAddMonoid.{u2} K (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_7))))))))) (Module.toMulActionWithZero.{u1, u2} A K (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_5)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_7)))))) (Algebra.toModule.{u1, u2} A K (CommRing.toCommSemiring.{u1} A _inst_5) (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_7))) _inst_8))))) (SMulZeroClass.toHasSmul.{u2, u3} K C (AddZeroClass.toHasZero.{u3} C (AddMonoid.toAddZeroClass.{u3} C (AddCommMonoid.toAddMonoid.{u3} C (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} C (Semiring.toNonAssocSemiring.{u3} C (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10)))))))) (SMulWithZero.toSmulZeroClass.{u2, u3} K C (MulZeroClass.toHasZero.{u2} K (MulZeroOneClass.toMulZeroClass.{u2} K (MonoidWithZero.toMulZeroOneClass.{u2} K (Semiring.toMonoidWithZero.{u2} K (CommSemiring.toSemiring.{u2} K (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_7))))))) (AddZeroClass.toHasZero.{u3} C (AddMonoid.toAddZeroClass.{u3} C (AddCommMonoid.toAddMonoid.{u3} C (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} C (Semiring.toNonAssocSemiring.{u3} C (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10)))))))) (MulActionWithZero.toSMulWithZero.{u2, u3} K C (Semiring.toMonoidWithZero.{u2} K (CommSemiring.toSemiring.{u2} K (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_7)))) (AddZeroClass.toHasZero.{u3} C (AddMonoid.toAddZeroClass.{u3} C (AddCommMonoid.toAddMonoid.{u3} C (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} C (Semiring.toNonAssocSemiring.{u3} C (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10)))))))) (Module.toMulActionWithZero.{u2, u3} K C (CommSemiring.toSemiring.{u2} K (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_7))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} C (Semiring.toNonAssocSemiring.{u3} C (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10))))) (Algebra.toModule.{u2, u3} K C (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_7)) (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10)) _inst_12))))) (SMulZeroClass.toHasSmul.{u1, u3} A C (AddZeroClass.toHasZero.{u3} C (AddMonoid.toAddZeroClass.{u3} C (AddCommMonoid.toAddMonoid.{u3} C (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} C (Semiring.toNonAssocSemiring.{u3} C (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10)))))))) (SMulWithZero.toSmulZeroClass.{u1, u3} A C (MulZeroClass.toHasZero.{u1} A (MulZeroOneClass.toMulZeroClass.{u1} A (MonoidWithZero.toMulZeroOneClass.{u1} A (Semiring.toMonoidWithZero.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_5)))))) (AddZeroClass.toHasZero.{u3} C (AddMonoid.toAddZeroClass.{u3} C (AddCommMonoid.toAddMonoid.{u3} C (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} C (Semiring.toNonAssocSemiring.{u3} C (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10)))))))) (MulActionWithZero.toSMulWithZero.{u1, u3} A C (Semiring.toMonoidWithZero.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_5))) (AddZeroClass.toHasZero.{u3} C (AddMonoid.toAddZeroClass.{u3} C (AddCommMonoid.toAddMonoid.{u3} C (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} C (Semiring.toNonAssocSemiring.{u3} C (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10)))))))) (Module.toMulActionWithZero.{u1, u3} A C (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_5)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} C (Semiring.toNonAssocSemiring.{u3} C (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10))))) (Algebra.toModule.{u1, u3} A C (CommRing.toCommSemiring.{u1} A _inst_5) (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10)) _inst_11)))))] {x : C}, Iff (IsAlgebraic.{u1, u3} A C _inst_5 (CommRing.toRing.{u3} C _inst_10) _inst_11 x) (IsAlgebraic.{u2, u3} K C (EuclideanDomain.toCommRing.{u2} K (Field.toEuclideanDomain.{u2} K _inst_7)) (CommRing.toRing.{u3} C _inst_10) _inst_12 x)
but is expected to have type
  forall (A : Type.{u3}) (K : Type.{u1}) (C : Type.{u2}) [_inst_5 : CommRing.{u3} A] [_inst_6 : IsDomain.{u3} A (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_5))] [_inst_7 : Field.{u1} K] [_inst_8 : Algebra.{u3, u1} A K (CommRing.toCommSemiring.{u3} A _inst_5) (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_7)))] [_inst_9 : IsFractionRing.{u3, u1} A _inst_5 K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7)) _inst_8] [_inst_10 : CommRing.{u2} C] [_inst_11 : Algebra.{u3, u2} A C (CommRing.toCommSemiring.{u3} A _inst_5) (CommSemiring.toSemiring.{u2} C (CommRing.toCommSemiring.{u2} C _inst_10))] [_inst_12 : Algebra.{u1, u2} K C (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_7)) (CommSemiring.toSemiring.{u2} C (CommRing.toCommSemiring.{u2} C _inst_10))] [_inst_13 : IsScalarTower.{u3, u1, u2} A K C (Algebra.toSMul.{u3, u1} A K (CommRing.toCommSemiring.{u3} A _inst_5) (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_7))) _inst_8) (Algebra.toSMul.{u1, u2} K C (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_7)) (CommSemiring.toSemiring.{u2} C (CommRing.toCommSemiring.{u2} C _inst_10)) _inst_12) (Algebra.toSMul.{u3, u2} A C (CommRing.toCommSemiring.{u3} A _inst_5) (CommSemiring.toSemiring.{u2} C (CommRing.toCommSemiring.{u2} C _inst_10)) _inst_11)] {x : C}, Iff (IsAlgebraic.{u3, u2} A C _inst_5 (CommRing.toRing.{u2} C _inst_10) _inst_11 x) (IsAlgebraic.{u1, u2} K C (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7)) (CommRing.toRing.{u2} C _inst_10) _inst_12 x)
Case conversion may be inaccurate. Consider using '#align is_fraction_ring.is_algebraic_iff IsFractionRing.isAlgebraic_iffₓ'. -/
/-- An element of a ring is algebraic over the ring `A` iff it is algebraic
over the field of fractions of `A`.
-/
theorem isAlgebraic_iff [Algebra A C] [Algebra K C] [IsScalarTower A K C] {x : C} :
    IsAlgebraic A x ↔ IsAlgebraic K x :=
  by
  constructor <;> rintro ⟨p, hp, px⟩
  · refine' ⟨p.map (algebraMap A K), fun h => hp (Polynomial.ext fun i => _), _⟩
    · have : algebraMap A K (p.coeff i) = 0 := trans (Polynomial.coeff_map _ _).symm (by simp [h])
      exact to_map_eq_zero_iff.mp this
    · exact (Polynomial.aeval_map_algebraMap K _ _).trans px
  ·
    exact
      ⟨integer_normalization _ p, mt integer_normalization_eq_zero_iff.mp hp,
        integer_normalization_aeval_eq_zero _ p px⟩
#align is_fraction_ring.is_algebraic_iff IsFractionRing.isAlgebraic_iff

variable {A K C}

/- warning: is_fraction_ring.comap_is_algebraic_iff -> IsFractionRing.comap_isAlgebraic_iff is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} {K : Type.{u2}} {C : Type.{u3}} [_inst_5 : CommRing.{u1} A] [_inst_6 : IsDomain.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_5))] [_inst_7 : Field.{u2} K] [_inst_8 : Algebra.{u1, u2} A K (CommRing.toCommSemiring.{u1} A _inst_5) (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_7)))] [_inst_9 : IsFractionRing.{u1, u2} A _inst_5 K (EuclideanDomain.toCommRing.{u2} K (Field.toEuclideanDomain.{u2} K _inst_7)) _inst_8] [_inst_10 : CommRing.{u3} C] [_inst_11 : Algebra.{u1, u3} A C (CommRing.toCommSemiring.{u1} A _inst_5) (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10))] [_inst_12 : Algebra.{u2, u3} K C (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_7)) (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10))] [_inst_13 : IsScalarTower.{u1, u2, u3} A K C (SMulZeroClass.toHasSmul.{u1, u2} A K (AddZeroClass.toHasZero.{u2} K (AddMonoid.toAddZeroClass.{u2} K (AddCommMonoid.toAddMonoid.{u2} K (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_7))))))))) (SMulWithZero.toSmulZeroClass.{u1, u2} A K (MulZeroClass.toHasZero.{u1} A (MulZeroOneClass.toMulZeroClass.{u1} A (MonoidWithZero.toMulZeroOneClass.{u1} A (Semiring.toMonoidWithZero.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_5)))))) (AddZeroClass.toHasZero.{u2} K (AddMonoid.toAddZeroClass.{u2} K (AddCommMonoid.toAddMonoid.{u2} K (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_7))))))))) (MulActionWithZero.toSMulWithZero.{u1, u2} A K (Semiring.toMonoidWithZero.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_5))) (AddZeroClass.toHasZero.{u2} K (AddMonoid.toAddZeroClass.{u2} K (AddCommMonoid.toAddMonoid.{u2} K (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_7))))))))) (Module.toMulActionWithZero.{u1, u2} A K (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_5)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u2} K (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u2} K (Semiring.toNonAssocSemiring.{u2} K (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_7)))))) (Algebra.toModule.{u1, u2} A K (CommRing.toCommSemiring.{u1} A _inst_5) (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_7))) _inst_8))))) (SMulZeroClass.toHasSmul.{u2, u3} K C (AddZeroClass.toHasZero.{u3} C (AddMonoid.toAddZeroClass.{u3} C (AddCommMonoid.toAddMonoid.{u3} C (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} C (Semiring.toNonAssocSemiring.{u3} C (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10)))))))) (SMulWithZero.toSmulZeroClass.{u2, u3} K C (MulZeroClass.toHasZero.{u2} K (MulZeroOneClass.toMulZeroClass.{u2} K (MonoidWithZero.toMulZeroOneClass.{u2} K (Semiring.toMonoidWithZero.{u2} K (CommSemiring.toSemiring.{u2} K (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_7))))))) (AddZeroClass.toHasZero.{u3} C (AddMonoid.toAddZeroClass.{u3} C (AddCommMonoid.toAddMonoid.{u3} C (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} C (Semiring.toNonAssocSemiring.{u3} C (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10)))))))) (MulActionWithZero.toSMulWithZero.{u2, u3} K C (Semiring.toMonoidWithZero.{u2} K (CommSemiring.toSemiring.{u2} K (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_7)))) (AddZeroClass.toHasZero.{u3} C (AddMonoid.toAddZeroClass.{u3} C (AddCommMonoid.toAddMonoid.{u3} C (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} C (Semiring.toNonAssocSemiring.{u3} C (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10)))))))) (Module.toMulActionWithZero.{u2, u3} K C (CommSemiring.toSemiring.{u2} K (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_7))) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} C (Semiring.toNonAssocSemiring.{u3} C (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10))))) (Algebra.toModule.{u2, u3} K C (Semifield.toCommSemiring.{u2} K (Field.toSemifield.{u2} K _inst_7)) (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10)) _inst_12))))) (SMulZeroClass.toHasSmul.{u1, u3} A C (AddZeroClass.toHasZero.{u3} C (AddMonoid.toAddZeroClass.{u3} C (AddCommMonoid.toAddMonoid.{u3} C (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} C (Semiring.toNonAssocSemiring.{u3} C (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10)))))))) (SMulWithZero.toSmulZeroClass.{u1, u3} A C (MulZeroClass.toHasZero.{u1} A (MulZeroOneClass.toMulZeroClass.{u1} A (MonoidWithZero.toMulZeroOneClass.{u1} A (Semiring.toMonoidWithZero.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_5)))))) (AddZeroClass.toHasZero.{u3} C (AddMonoid.toAddZeroClass.{u3} C (AddCommMonoid.toAddMonoid.{u3} C (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} C (Semiring.toNonAssocSemiring.{u3} C (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10)))))))) (MulActionWithZero.toSMulWithZero.{u1, u3} A C (Semiring.toMonoidWithZero.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_5))) (AddZeroClass.toHasZero.{u3} C (AddMonoid.toAddZeroClass.{u3} C (AddCommMonoid.toAddMonoid.{u3} C (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} C (Semiring.toNonAssocSemiring.{u3} C (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10)))))))) (Module.toMulActionWithZero.{u1, u3} A C (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_5)) (NonUnitalNonAssocSemiring.toAddCommMonoid.{u3} C (NonAssocSemiring.toNonUnitalNonAssocSemiring.{u3} C (Semiring.toNonAssocSemiring.{u3} C (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10))))) (Algebra.toModule.{u1, u3} A C (CommRing.toCommSemiring.{u1} A _inst_5) (Ring.toSemiring.{u3} C (CommRing.toRing.{u3} C _inst_10)) _inst_11)))))], Iff (Algebra.IsAlgebraic.{u1, u3} A C _inst_5 (CommRing.toRing.{u3} C _inst_10) _inst_11) (Algebra.IsAlgebraic.{u2, u3} K C (EuclideanDomain.toCommRing.{u2} K (Field.toEuclideanDomain.{u2} K _inst_7)) (CommRing.toRing.{u3} C _inst_10) _inst_12)
but is expected to have type
  forall {A : Type.{u3}} {K : Type.{u1}} {C : Type.{u2}} [_inst_5 : CommRing.{u3} A] [_inst_6 : IsDomain.{u3} A (CommSemiring.toSemiring.{u3} A (CommRing.toCommSemiring.{u3} A _inst_5))] [_inst_7 : Field.{u1} K] [_inst_8 : Algebra.{u3, u1} A K (CommRing.toCommSemiring.{u3} A _inst_5) (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_7)))] [_inst_9 : IsFractionRing.{u3, u1} A _inst_5 K (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7)) _inst_8] [_inst_10 : CommRing.{u2} C] [_inst_11 : Algebra.{u3, u2} A C (CommRing.toCommSemiring.{u3} A _inst_5) (CommSemiring.toSemiring.{u2} C (CommRing.toCommSemiring.{u2} C _inst_10))] [_inst_12 : Algebra.{u1, u2} K C (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_7)) (CommSemiring.toSemiring.{u2} C (CommRing.toCommSemiring.{u2} C _inst_10))] [_inst_13 : IsScalarTower.{u3, u1, u2} A K C (Algebra.toSMul.{u3, u1} A K (CommRing.toCommSemiring.{u3} A _inst_5) (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_7))) _inst_8) (Algebra.toSMul.{u1, u2} K C (Semifield.toCommSemiring.{u1} K (Field.toSemifield.{u1} K _inst_7)) (CommSemiring.toSemiring.{u2} C (CommRing.toCommSemiring.{u2} C _inst_10)) _inst_12) (Algebra.toSMul.{u3, u2} A C (CommRing.toCommSemiring.{u3} A _inst_5) (CommSemiring.toSemiring.{u2} C (CommRing.toCommSemiring.{u2} C _inst_10)) _inst_11)], Iff (Algebra.IsAlgebraic.{u3, u2} A C _inst_5 (CommRing.toRing.{u2} C _inst_10) _inst_11) (Algebra.IsAlgebraic.{u1, u2} K C (EuclideanDomain.toCommRing.{u1} K (Field.toEuclideanDomain.{u1} K _inst_7)) (CommRing.toRing.{u2} C _inst_10) _inst_12)
Case conversion may be inaccurate. Consider using '#align is_fraction_ring.comap_is_algebraic_iff IsFractionRing.comap_isAlgebraic_iffₓ'. -/
/-- A ring is algebraic over the ring `A` iff it is algebraic over the field of fractions of `A`.
-/
theorem comap_isAlgebraic_iff [Algebra A C] [Algebra K C] [IsScalarTower A K C] :
    Algebra.IsAlgebraic A C ↔ Algebra.IsAlgebraic K C :=
  ⟨fun h x => (isAlgebraic_iff A K C).mp (h x), fun h x => (isAlgebraic_iff A K C).mpr (h x)⟩
#align is_fraction_ring.comap_is_algebraic_iff IsFractionRing.comap_isAlgebraic_iff

end IsFractionRing

open IsLocalization

section IsIntegral

variable {R S} {Rₘ Sₘ : Type _} [CommRing Rₘ] [CommRing Sₘ]

variable [Algebra R Rₘ] [IsLocalization M Rₘ]

variable [Algebra S Sₘ] [IsLocalization (Algebra.algebraMapSubmonoid S M) Sₘ]

variable {S M}

open Polynomial

/- warning: ring_hom.is_integral_elem_localization_at_leading_coeff -> RingHom.isIntegralElem_localization_at_leadingCoeff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align ring_hom.is_integral_elem_localization_at_leading_coeff RingHom.isIntegralElem_localization_at_leadingCoeffₓ'. -/
theorem RingHom.isIntegralElem_localization_at_leadingCoeff {R S : Type _} [CommRing R] [CommRing S]
    (f : R →+* S) (x : S) (p : R[X]) (hf : p.eval₂ f x = 0) (M : Submonoid R)
    (hM : p.leadingCoeff ∈ M) {Rₘ Sₘ : Type _} [CommRing Rₘ] [CommRing Sₘ] [Algebra R Rₘ]
    [IsLocalization M Rₘ] [Algebra S Sₘ] [IsLocalization (M.map f : Submonoid S) Sₘ] :
    (map Sₘ f M.le_comap_map : Rₘ →+* _).IsIntegralElem (algebraMap S Sₘ x) :=
  by
  by_cases triv : (1 : Rₘ) = 0
  · exact ⟨0, ⟨trans leading_coeff_zero triv.symm, eval₂_zero _ _⟩⟩
  haveI : Nontrivial Rₘ := nontrivial_of_ne 1 0 triv
  obtain ⟨b, hb⟩ := is_unit_iff_exists_inv.mp (map_units Rₘ ⟨p.leading_coeff, hM⟩)
  refine' ⟨p.map (algebraMap R Rₘ) * C b, ⟨_, _⟩⟩
  · refine' monic_mul_C_of_leading_coeff_mul_eq_one _
    rwa [leading_coeff_map_of_leading_coeff_ne_zero (algebraMap R Rₘ)]
    refine' fun hfp => zero_ne_one (trans (MulZeroClass.zero_mul b).symm (hfp ▸ hb) : (0 : Rₘ) = 1)
  · refine' eval₂_mul_eq_zero_of_left _ _ _ _
    erw [eval₂_map, IsLocalization.map_comp, ← hom_eval₂ _ f (algebraMap S Sₘ) x]
    exact trans (congr_arg (algebraMap S Sₘ) hf) (RingHom.map_zero _)
#align ring_hom.is_integral_elem_localization_at_leading_coeff RingHom.isIntegralElem_localization_at_leadingCoeff

/- warning: is_integral_localization_at_leading_coeff -> is_integral_localization_at_leadingCoeff is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_integral_localization_at_leading_coeff is_integral_localization_at_leadingCoeffₓ'. -/
/-- Given a particular witness to an element being algebraic over an algebra `R → S`,
We can localize to a submonoid containing the leading coefficient to make it integral.
Explicitly, the map between the localizations will be an integral ring morphism -/
theorem is_integral_localization_at_leadingCoeff {x : S} (p : R[X]) (hp : aeval x p = 0)
    (hM : p.leadingCoeff ∈ M) :
    (map Sₘ (algebraMap R S)
            (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
          Rₘ →+* _).IsIntegralElem
      (algebraMap S Sₘ x) :=
  (algebraMap R S).isIntegralElem_localization_at_leadingCoeff x p hp M hM
#align is_integral_localization_at_leading_coeff is_integral_localization_at_leadingCoeff

/- warning: is_integral_localization -> isIntegral_localization is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_integral_localization isIntegral_localizationₓ'. -/
/-- If `R → S` is an integral extension, `M` is a submonoid of `R`,
`Rₘ` is the localization of `R` at `M`,
and `Sₘ` is the localization of `S` at the image of `M` under the extension map,
then the induced map `Rₘ → Sₘ` is also an integral extension -/
theorem isIntegral_localization (H : Algebra.IsIntegral R S) :
    (map Sₘ (algebraMap R S)
          (show _ ≤ (Algebra.algebraMapSubmonoid S M).comap _ from M.le_comap_map) :
        Rₘ →+* _).IsIntegral :=
  by
  intro x
  obtain ⟨⟨s, ⟨u, hu⟩⟩, hx⟩ := surj (Algebra.algebraMapSubmonoid S M) x
  obtain ⟨v, hv⟩ := hu
  obtain ⟨v', hv'⟩ := isUnit_iff_exists_inv'.1 (map_units Rₘ ⟨v, hv.1⟩)
  refine'
    @isIntegral_of_isIntegral_mul_unit Rₘ _ _ _ (localizationAlgebra M S) x (algebraMap S Sₘ u) v' _
      _
  · replace hv' := congr_arg (@algebraMap Rₘ Sₘ _ _ (localizationAlgebra M S)) hv'
    rw [RingHom.map_mul, RingHom.map_one, ← RingHom.comp_apply _ (algebraMap R Rₘ)] at hv'
    erw [IsLocalization.map_comp] at hv'
    exact hv.2 ▸ hv'
  · obtain ⟨p, hp⟩ := H s
    exact hx.symm ▸ is_integral_localization_at_leadingCoeff p hp.2 (hp.1.symm ▸ M.one_mem)
#align is_integral_localization isIntegral_localization

/- warning: is_integral_localization' -> isIntegral_localization' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_integral_localization' isIntegral_localization'ₓ'. -/
theorem isIntegral_localization' {R S : Type _} [CommRing R] [CommRing S] {f : R →+* S}
    (hf : f.IsIntegral) (M : Submonoid R) :
    (map (Localization (M.map (f : R →* S))) f
          (M.le_comap_map : _ ≤ Submonoid.comap (f : R →* S) _) :
        Localization M →+* _).IsIntegral :=
  @isIntegral_localization R _ M S _ f.toAlgebra _ _ _ _ _ _ _ _ hf
#align is_integral_localization' isIntegral_localization'

variable (M)

/- warning: is_localization.scale_roots_common_denom_mem_lifts -> IsLocalization.scaleRoots_commonDenom_mem_lifts is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_localization.scale_roots_common_denom_mem_lifts IsLocalization.scaleRoots_commonDenom_mem_liftsₓ'. -/
theorem IsLocalization.scaleRoots_commonDenom_mem_lifts (p : Rₘ[X])
    (hp : p.leadingCoeff ∈ (algebraMap R Rₘ).range) :
    p.scaleRoots (algebraMap R Rₘ <| IsLocalization.commonDenom M p.support p.coeff) ∈
      Polynomial.lifts (algebraMap R Rₘ) :=
  by
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  rw [Polynomial.coeff_scaleRoots]
  by_cases h₁ : n ∈ p.support
  by_cases h₂ : n = p.nat_degree
  · rwa [h₂, Polynomial.coeff_natDegree, tsub_self, pow_zero, _root_.mul_one]
  · have : n + 1 ≤ p.nat_degree := lt_of_le_of_ne (Polynomial.le_natDegree_of_mem_supp _ h₁) h₂
    rw [← tsub_add_cancel_of_le (le_tsub_of_add_le_left this), pow_add, pow_one, mul_comm,
      _root_.mul_assoc, ← map_pow]
    change _ ∈ (algebraMap R Rₘ).range
    apply mul_mem
    · exact RingHom.mem_range_self _ _
    · rw [← Algebra.smul_def]
      exact ⟨_, IsLocalization.map_integerMultiple M p.support p.coeff ⟨n, h₁⟩⟩
  · rw [Polynomial.not_mem_support_iff] at h₁
    rw [h₁, MulZeroClass.zero_mul]
    exact zero_mem (algebraMap R Rₘ).range
#align is_localization.scale_roots_common_denom_mem_lifts IsLocalization.scaleRoots_commonDenom_mem_lifts

/- warning: is_integral.exists_multiple_integral_of_is_localization -> IsIntegral.exists_multiple_integral_of_isLocalization is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_integral.exists_multiple_integral_of_is_localization IsIntegral.exists_multiple_integral_of_isLocalizationₓ'. -/
theorem IsIntegral.exists_multiple_integral_of_isLocalization [Algebra Rₘ S] [IsScalarTower R Rₘ S]
    (x : S) (hx : IsIntegral Rₘ x) : ∃ m : M, IsIntegral R (m • x) :=
  by
  cases' subsingleton_or_nontrivial Rₘ with _ nontriv <;> skip
  · haveI := (algebraMap Rₘ S).codomain_trivial
    exact ⟨1, Polynomial.X, Polynomial.monic_X, Subsingleton.elim _ _⟩
  obtain ⟨p, hp₁, hp₂⟩ := hx
  obtain ⟨p', hp'₁, -, hp'₂⟩ :=
    lifts_and_nat_degree_eq_and_monic (IsLocalization.scaleRoots_commonDenom_mem_lifts M p _) _
  · refine' ⟨IsLocalization.commonDenom M p.support p.coeff, p', hp'₂, _⟩
    rw [IsScalarTower.algebraMap_eq R Rₘ S, ← Polynomial.eval₂_map, hp'₁, Submonoid.smul_def,
      Algebra.smul_def, IsScalarTower.algebraMap_apply R Rₘ S]
    exact Polynomial.scaleRoots_eval₂_eq_zero _ hp₂
  · rw [hp₁.leading_coeff]
    exact one_mem _
  · rwa [Polynomial.monic_scaleRoots_iff]
#align is_integral.exists_multiple_integral_of_is_localization IsIntegral.exists_multiple_integral_of_isLocalization

end IsIntegral

variable {A K : Type _} [CommRing A] [IsDomain A]

namespace IsIntegralClosure

variable (A) {L : Type _} [Field K] [Field L] [Algebra A K] [Algebra A L] [IsFractionRing A K]

variable (C : Type _) [CommRing C] [IsDomain C] [Algebra C L] [IsIntegralClosure C A L]

variable [Algebra A C] [IsScalarTower A C L]

open Algebra

/- warning: is_integral_closure.is_fraction_ring_of_algebraic -> IsIntegralClosure.isFractionRing_of_algebraic is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_integral_closure.is_fraction_ring_of_algebraic IsIntegralClosure.isFractionRing_of_algebraicₓ'. -/
/-- If the field `L` is an algebraic extension of the integral domain `A`,
the integral closure `C` of `A` in `L` has fraction field `L`. -/
theorem isFractionRing_of_algebraic (alg : IsAlgebraic A L)
    (inj : ∀ x, algebraMap A L x = 0 → x = 0) : IsFractionRing C L :=
  { map_units := fun ⟨y, hy⟩ =>
      IsUnit.mk0 _
        (show algebraMap C L y ≠ 0 from fun h =>
          mem_nonZeroDivisors_iff_ne_zero.mp hy
            ((injective_iff_map_eq_zero (algebraMap C L)).mp (algebraMap_injective C A L) _ h))
    surj := fun z =>
      let ⟨x, y, hy, hxy⟩ := exists_integral_multiple (alg z) inj
      ⟨⟨mk' C (x : L) x.2, algebraMap _ _ y,
          mem_nonZeroDivisors_iff_ne_zero.mpr fun h =>
            hy (inj _ (by rw [IsScalarTower.algebraMap_apply A C L, h, RingHom.map_zero]))⟩,
        by rw [[anonymous], algebra_map_mk', ← IsScalarTower.algebraMap_apply A C L, hxy]⟩
    eq_iff_exists := fun x y =>
      ⟨fun h => ⟨1, by simpa using algebra_map_injective C A L h⟩, fun ⟨c, hc⟩ =>
        congr_arg (algebraMap _ L) (mul_left_cancel₀ (mem_nonZeroDivisors_iff_ne_zero.mp c.2) hc)⟩ }
#align is_integral_closure.is_fraction_ring_of_algebraic IsIntegralClosure.isFractionRing_of_algebraic

variable (K L)

/- warning: is_integral_closure.is_fraction_ring_of_finite_extension -> IsIntegralClosure.isFractionRing_of_finite_extension is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_integral_closure.is_fraction_ring_of_finite_extension IsIntegralClosure.isFractionRing_of_finite_extensionₓ'. -/
/-- If the field `L` is a finite extension of the fraction field of the integral domain `A`,
the integral closure `C` of `A` in `L` has fraction field `L`. -/
theorem isFractionRing_of_finite_extension [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] : IsFractionRing C L :=
  isFractionRing_of_algebraic A C
    (IsFractionRing.comap_isAlgebraic_iff.mpr (isAlgebraic_of_finite K L)) fun x hx =>
    IsFractionRing.to_map_eq_zero_iff.mp
      ((map_eq_zero <| algebraMap K L).mp <| (IsScalarTower.algebraMap_apply _ _ _ _).symm.trans hx)
#align is_integral_closure.is_fraction_ring_of_finite_extension IsIntegralClosure.isFractionRing_of_finite_extension

end IsIntegralClosure

namespace integralClosure

variable {L : Type _} [Field K] [Field L] [Algebra A K] [IsFractionRing A K]

open Algebra

/- warning: integral_closure.is_fraction_ring_of_algebraic -> integralClosure.isFractionRing_of_algebraic is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align integral_closure.is_fraction_ring_of_algebraic integralClosure.isFractionRing_of_algebraicₓ'. -/
/-- If the field `L` is an algebraic extension of the integral domain `A`,
the integral closure of `A` in `L` has fraction field `L`. -/
theorem isFractionRing_of_algebraic [Algebra A L] (alg : IsAlgebraic A L)
    (inj : ∀ x, algebraMap A L x = 0 → x = 0) : IsFractionRing (integralClosure A L) L :=
  IsIntegralClosure.isFractionRing_of_algebraic A (integralClosure A L) alg inj
#align integral_closure.is_fraction_ring_of_algebraic integralClosure.isFractionRing_of_algebraic

variable (K L)

/- warning: integral_closure.is_fraction_ring_of_finite_extension -> integralClosure.isFractionRing_of_finite_extension is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align integral_closure.is_fraction_ring_of_finite_extension integralClosure.isFractionRing_of_finite_extensionₓ'. -/
/-- If the field `L` is a finite extension of the fraction field of the integral domain `A`,
the integral closure of `A` in `L` has fraction field `L`. -/
theorem isFractionRing_of_finite_extension [Algebra A L] [Algebra K L] [IsScalarTower A K L]
    [FiniteDimensional K L] : IsFractionRing (integralClosure A L) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension A K L (integralClosure A L)
#align integral_closure.is_fraction_ring_of_finite_extension integralClosure.isFractionRing_of_finite_extension

end integralClosure

namespace IsFractionRing

variable (R S K)

/- warning: is_fraction_ring.is_algebraic_iff' -> IsFractionRing.isAlgebraic_iff' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_fraction_ring.is_algebraic_iff' IsFractionRing.isAlgebraic_iff'ₓ'. -/
/-- `S` is algebraic over `R` iff a fraction ring of `S` is algebraic over `R` -/
theorem isAlgebraic_iff' [Field K] [IsDomain R] [IsDomain S] [Algebra R K] [Algebra S K]
    [NoZeroSMulDivisors R K] [IsFractionRing S K] [IsScalarTower R S K] :
    Algebra.IsAlgebraic R S ↔ Algebra.IsAlgebraic R K :=
  by
  simp only [Algebra.IsAlgebraic]
  constructor
  · intro h x
    rw [IsFractionRing.isAlgebraic_iff R (FractionRing R) K, isAlgebraic_iff_isIntegral]
    obtain ⟨a : S, b, ha, rfl⟩ := @div_surjective S _ _ _ _ _ _ x
    obtain ⟨f, hf₁, hf₂⟩ := h b
    rw [div_eq_mul_inv]
    refine' isIntegral_mul _ _
    · rw [← isAlgebraic_iff_isIntegral]
      refine'
        _root_.is_algebraic_of_larger_base_of_injective
          (NoZeroSMulDivisors.algebraMap_injective R (FractionRing R)) _
      exact isAlgebraic_algebraMap_of_isAlgebraic (h a)
    · rw [← isAlgebraic_iff_isIntegral]
      use (f.map (algebraMap R (FractionRing R))).reverse
      constructor
      ·
        rwa [Ne.def, Polynomial.reverse_eq_zero, ← Polynomial.degree_eq_bot,
          Polynomial.degree_map_eq_of_injective
            (NoZeroSMulDivisors.algebraMap_injective R (FractionRing R)),
          Polynomial.degree_eq_bot]
      · have : Invertible (algebraMap S K b) :=
          IsUnit.invertible
            (isUnit_of_mem_nonZeroDivisors
              (mem_nonZeroDivisors_iff_ne_zero.2 fun h =>
                nonZeroDivisors.ne_zero ha
                  ((injective_iff_map_eq_zero (algebraMap S K)).1
                    (NoZeroSMulDivisors.algebraMap_injective _ _) b h)))
        rw [Polynomial.aeval_def, ← invOf_eq_inv, Polynomial.eval₂_reverse_eq_zero_iff,
          Polynomial.eval₂_map, ← IsScalarTower.algebraMap_eq, ← Polynomial.aeval_def,
          Polynomial.aeval_algebraMap_apply, hf₂, RingHom.map_zero]
  · intro h x
    obtain ⟨f, hf₁, hf₂⟩ := h (algebraMap S K x)
    use f, hf₁
    rw [Polynomial.aeval_algebraMap_apply] at hf₂
    exact
      (injective_iff_map_eq_zero (algebraMap S K)).1 (NoZeroSMulDivisors.algebraMap_injective _ _) _
        hf₂
#align is_fraction_ring.is_algebraic_iff' IsFractionRing.isAlgebraic_iff'

open nonZeroDivisors

variable (R) {S K}

/- warning: is_fraction_ring.ideal_span_singleton_map_subset -> IsFractionRing.ideal_span_singleton_map_subset is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_fraction_ring.ideal_span_singleton_map_subset IsFractionRing.ideal_span_singleton_map_subsetₓ'. -/
/-- If the `S`-multiples of `a` are contained in some `R`-span, then `Frac(S)`-multiples of `a`
are contained in the equivalent `Frac(R)`-span. -/
theorem ideal_span_singleton_map_subset {L : Type _} [IsDomain R] [IsDomain S] [Field K] [Field L]
    [Algebra R K] [Algebra R L] [Algebra S L] [IsIntegralClosure S R L] [IsFractionRing S L]
    [Algebra K L] [IsScalarTower R S L] [IsScalarTower R K L] {a : S} {b : Set S}
    (alg : Algebra.IsAlgebraic R L) (inj : Function.Injective (algebraMap R L))
    (h : (Ideal.span ({a} : Set S) : Set S) ⊆ Submodule.span R b) :
    (Ideal.span ({algebraMap S L a} : Set L) : Set L) ⊆ Submodule.span K (algebraMap S L '' b) :=
  by
  intro x hx
  obtain ⟨x', rfl⟩ := ideal.mem_span_singleton.mp hx
  obtain ⟨y', z', rfl⟩ := IsLocalization.mk'_surjective S⁰ x'
  obtain ⟨y, z, hz0, yz_eq⟩ :=
    IsIntegralClosure.exists_smul_eq_mul alg inj y' (nonZeroDivisors.coe_ne_zero z')
  have injRS : Function.Injective (algebraMap R S) :=
    by
    refine'
      Function.Injective.of_comp (show Function.Injective (algebraMap S L ∘ algebraMap R S) from _)
    rwa [← RingHom.coe_comp, ← IsScalarTower.algebraMap_eq]
  have hz0' : algebraMap R S z ∈ S⁰ :=
    map_mem_nonZeroDivisors (algebraMap R S) injRS (mem_nonZeroDivisors_of_ne_zero hz0)
  have mk_yz_eq : IsLocalization.mk' L y' z' = IsLocalization.mk' L y ⟨_, hz0'⟩ :=
    by
    rw [Algebra.smul_def, mul_comm _ y, mul_comm _ y', ← [anonymous] (algebraMap R S z) hz0'] at
      yz_eq
    exact IsLocalization.mk'_eq_of_eq (by rw [mul_comm _ y, mul_comm _ y', yz_eq])
  suffices hy : algebraMap S L (a * y) ∈ Submodule.span K (⇑(algebraMap S L) '' b)
  · rw [mk_yz_eq, IsFractionRing.mk'_eq_div, [anonymous], ← IsScalarTower.algebraMap_apply,
      IsScalarTower.algebraMap_apply R K L, div_eq_mul_inv, ← mul_assoc, mul_comm, ← map_inv₀, ←
      Algebra.smul_def, ← _root_.map_mul]
    exact (Submodule.span K _).smul_mem _ hy
  refine' Submodule.span_subset_span R K _ _
  rw [Submodule.span_algebraMap_image_of_tower]
  exact Submodule.mem_map_of_mem (h (ideal.mem_span_singleton.mpr ⟨y, rfl⟩))
#align is_fraction_ring.ideal_span_singleton_map_subset IsFractionRing.ideal_span_singleton_map_subset

end IsFractionRing

