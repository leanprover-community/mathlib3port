/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Mario Carneiro, Johan Commelin, Amelia Livingston, Anne Baanen

! This file was ported from Lean 3 source module ring_theory.localization.num_denom
! leanprover-community/mathlib commit 97eab48559068f3d6313da387714ef25768fb730
! Please do not edit these lines, except to modify the commit id
! if you have ported upstream changes.
-/
import Mathbin.RingTheory.Localization.FractionRing
import Mathbin.RingTheory.Localization.Integer
import Mathbin.RingTheory.UniqueFactorizationDomain

/-!
# Numerator and denominator in a localization

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

namespace IsFractionRing

open IsLocalization

section NumDenom

variable (A : Type _) [CommRing A] [IsDomain A] [UniqueFactorizationMonoid A]

variable {K : Type _} [Field K] [Algebra A K] [IsFractionRing A K]

/- warning: is_fraction_ring.exists_reduced_fraction -> IsFractionRing.exists_reduced_fraction is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_fraction_ring.exists_reduced_fraction IsFractionRing.exists_reduced_fractionₓ'. -/
theorem exists_reduced_fraction (x : K) :
    ∃ (a : A)(b : nonZeroDivisors A), (∀ {d}, d ∣ a → d ∣ b → IsUnit d) ∧ mk' K a b = x :=
  by
  obtain ⟨⟨b, b_nonzero⟩, a, hab⟩ := exists_integer_multiple (nonZeroDivisors A) x
  obtain ⟨a', b', c', no_factor, rfl, rfl⟩ :=
    UniqueFactorizationMonoid.exists_reduced_factors' a b
      (mem_non_zero_divisors_iff_ne_zero.mp b_nonzero)
  obtain ⟨c'_nonzero, b'_nonzero⟩ := mul_mem_non_zero_divisors.mp b_nonzero
  refine' ⟨a', ⟨b', b'_nonzero⟩, @no_factor, _⟩
  refine' mul_left_cancel₀ (IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b_nonzero) _
  simp only [Subtype.coe_mk, RingHom.map_mul, Algebra.smul_def] at *
  erw [← hab, mul_assoc, mk'_spec' _ a' ⟨b', b'_nonzero⟩]
#align is_fraction_ring.exists_reduced_fraction IsFractionRing.exists_reduced_fraction

#print IsFractionRing.num /-
/-- `f.num x` is the numerator of `x : f.codomain` as a reduced fraction. -/
noncomputable def num (x : K) : A :=
  Classical.choose (exists_reduced_fraction A x)
#align is_fraction_ring.num IsFractionRing.num
-/

/- warning: is_fraction_ring.denom -> IsFractionRing.den is a dubious translation:
lean 3 declaration is
  forall (A : Type.{u1}) [_inst_5 : CommRing.{u1} A] [_inst_6 : IsDomain.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_5))] [_inst_7 : UniqueFactorizationMonoid.{u1} A (IsDomain.toCancelCommMonoidWithZero.{u1} A (CommRing.toCommSemiring.{u1} A _inst_5) _inst_6)] {K : Type.{u2}} [_inst_8 : Field.{u2} K] [_inst_9 : Algebra.{u1, u2} A K (CommRing.toCommSemiring.{u1} A _inst_5) (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_8)))] [_inst_10 : IsFractionRing.{u1, u2} A _inst_5 K (Field.toCommRing.{u2} K _inst_8) _inst_9], K -> (coeSort.{succ u1, succ (succ u1)} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (MonoidWithZero.toMulZeroOneClass.{u1} A (Semiring.toMonoidWithZero.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_5)))))) Type.{u1} (SetLike.hasCoeToSort.{u1, u1} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (MonoidWithZero.toMulZeroOneClass.{u1} A (Semiring.toMonoidWithZero.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_5)))))) A (Submonoid.setLike.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (MonoidWithZero.toMulZeroOneClass.{u1} A (Semiring.toMonoidWithZero.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_5))))))) (nonZeroDivisors.{u1} A (Semiring.toMonoidWithZero.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_5)))))
but is expected to have type
  forall (A : Type.{u1}) [_inst_5 : CommRing.{u1} A] [_inst_6 : IsDomain.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_5))] [_inst_7 : UniqueFactorizationMonoid.{u1} A (IsDomain.toCancelCommMonoidWithZero.{u1} A (CommRing.toCommSemiring.{u1} A _inst_5) _inst_6)] {K : Type.{u2}} [_inst_8 : Field.{u2} K] [_inst_9 : Algebra.{u1, u2} A K (CommRing.toCommSemiring.{u1} A _inst_5) (DivisionSemiring.toSemiring.{u2} K (Semifield.toDivisionSemiring.{u2} K (Field.toSemifield.{u2} K _inst_8)))] [_inst_10 : IsFractionRing.{u1, u2} A _inst_5 K (Field.toCommRing.{u2} K _inst_8) _inst_9], K -> (Subtype.{succ u1} A (fun (x : A) => Membership.mem.{u1, u1} A (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (MonoidWithZero.toMulZeroOneClass.{u1} A (Semiring.toMonoidWithZero.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_5)))))) (SetLike.instMembership.{u1, u1} (Submonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (MonoidWithZero.toMulZeroOneClass.{u1} A (Semiring.toMonoidWithZero.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_5)))))) A (Submonoid.instSetLikeSubmonoid.{u1} A (MulZeroOneClass.toMulOneClass.{u1} A (MonoidWithZero.toMulZeroOneClass.{u1} A (Semiring.toMonoidWithZero.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_5))))))) x (nonZeroDivisors.{u1} A (Semiring.toMonoidWithZero.{u1} A (CommSemiring.toSemiring.{u1} A (CommRing.toCommSemiring.{u1} A _inst_5))))))
Case conversion may be inaccurate. Consider using '#align is_fraction_ring.denom IsFractionRing.denₓ'. -/
/-- `f.num x` is the denominator of `x : f.codomain` as a reduced fraction. -/
noncomputable def den (x : K) : nonZeroDivisors A :=
  Classical.choose (Classical.choose_spec (exists_reduced_fraction A x))
#align is_fraction_ring.denom IsFractionRing.den

/- warning: is_fraction_ring.num_denom_reduced -> IsFractionRing.num_den_reduced is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_fraction_ring.num_denom_reduced IsFractionRing.num_den_reducedₓ'. -/
theorem num_den_reduced (x : K) {d} : d ∣ num A x → d ∣ den A x → IsUnit d :=
  (Classical.choose_spec (Classical.choose_spec (exists_reduced_fraction A x))).1
#align is_fraction_ring.num_denom_reduced IsFractionRing.num_den_reduced

#print IsFractionRing.mk'_num_den /-
@[simp]
theorem mk'_num_den (x : K) : mk' K (num A x) (den A x) = x :=
  (Classical.choose_spec (Classical.choose_spec (exists_reduced_fraction A x))).2
#align is_fraction_ring.mk'_num_denom IsFractionRing.mk'_num_den
-/

variable {A}

/- warning: is_fraction_ring.num_mul_denom_eq_num_iff_eq -> IsFractionRing.num_mul_den_eq_num_iff_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_fraction_ring.num_mul_denom_eq_num_iff_eq IsFractionRing.num_mul_den_eq_num_iff_eqₓ'. -/
theorem num_mul_den_eq_num_iff_eq {x y : K} :
    x * algebraMap A K (den A y) = algebraMap A K (num A y) ↔ x = y :=
  ⟨fun h => by simpa only [mk'_num_denom] using eq_mk'_iff_mul_eq.mpr h, fun h =>
    eq_mk'_iff_mul_eq.mp (by rw [h, mk'_num_denom])⟩
#align is_fraction_ring.num_mul_denom_eq_num_iff_eq IsFractionRing.num_mul_den_eq_num_iff_eq

/- warning: is_fraction_ring.num_mul_denom_eq_num_iff_eq' -> IsFractionRing.num_mul_den_eq_num_iff_eq' is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_fraction_ring.num_mul_denom_eq_num_iff_eq' IsFractionRing.num_mul_den_eq_num_iff_eq'ₓ'. -/
theorem num_mul_den_eq_num_iff_eq' {x y : K} :
    y * algebraMap A K (den A x) = algebraMap A K (num A x) ↔ x = y :=
  ⟨fun h => by simpa only [eq_comm, mk'_num_denom] using eq_mk'_iff_mul_eq.mpr h, fun h =>
    eq_mk'_iff_mul_eq.mp (by rw [h, mk'_num_denom])⟩
#align is_fraction_ring.num_mul_denom_eq_num_iff_eq' IsFractionRing.num_mul_den_eq_num_iff_eq'

/- warning: is_fraction_ring.num_mul_denom_eq_num_mul_denom_iff_eq -> IsFractionRing.num_mul_den_eq_num_mul_den_iff_eq is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_fraction_ring.num_mul_denom_eq_num_mul_denom_iff_eq IsFractionRing.num_mul_den_eq_num_mul_den_iff_eqₓ'. -/
theorem num_mul_den_eq_num_mul_den_iff_eq {x y : K} :
    num A y * den A x = num A x * den A y ↔ x = y :=
  ⟨fun h => by simpa only [mk'_num_denom] using mk'_eq_of_eq' h, fun h => by rw [h]⟩
#align is_fraction_ring.num_mul_denom_eq_num_mul_denom_iff_eq IsFractionRing.num_mul_den_eq_num_mul_den_iff_eq

/- warning: is_fraction_ring.eq_zero_of_num_eq_zero -> IsFractionRing.eq_zero_of_num_eq_zero is a dubious translation:
lean 3 declaration is
  forall {A : Type.{u1}} [_inst_5 : CommRing.{u1} A] [_inst_6 : IsDomain.{u1} A (Ring.toSemiring.{u1} A (CommRing.toRing.{u1} A _inst_5))] [_inst_7 : UniqueFactorizationMonoid.{u1} A (IsDomain.toCancelCommMonoidWithZero.{u1} A (CommRing.toCommSemiring.{u1} A _inst_5) _inst_6)] {K : Type.{u2}} [_inst_8 : Field.{u2} K] [_inst_9 : Algebra.{u1, u2} A K (CommRing.toCommSemiring.{u1} A _inst_5) (Ring.toSemiring.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_8)))] [_inst_10 : IsFractionRing.{u1, u2} A _inst_5 K (Field.toCommRing.{u2} K _inst_8) _inst_9] {x : K}, (Eq.{succ u1} A (IsFractionRing.num.{u1, u2} A _inst_5 _inst_6 _inst_7 K _inst_8 _inst_9 _inst_10 x) (OfNat.ofNat.{u1} A 0 (OfNat.mk.{u1} A 0 (Zero.zero.{u1} A (MulZeroClass.toHasZero.{u1} A (NonUnitalNonAssocSemiring.toMulZeroClass.{u1} A (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u1} A (NonAssocRing.toNonUnitalNonAssocRing.{u1} A (Ring.toNonAssocRing.{u1} A (CommRing.toRing.{u1} A _inst_5)))))))))) -> (Eq.{succ u2} K x (OfNat.ofNat.{u2} K 0 (OfNat.mk.{u2} K 0 (Zero.zero.{u2} K (MulZeroClass.toHasZero.{u2} K (NonUnitalNonAssocSemiring.toMulZeroClass.{u2} K (NonUnitalNonAssocRing.toNonUnitalNonAssocSemiring.{u2} K (NonAssocRing.toNonUnitalNonAssocRing.{u2} K (Ring.toNonAssocRing.{u2} K (DivisionRing.toRing.{u2} K (Field.toDivisionRing.{u2} K _inst_8)))))))))))
but is expected to have type
  forall {A : Type.{u2}} [_inst_5 : CommRing.{u2} A] [_inst_6 : IsDomain.{u2} A (CommSemiring.toSemiring.{u2} A (CommRing.toCommSemiring.{u2} A _inst_5))] [_inst_7 : UniqueFactorizationMonoid.{u2} A (IsDomain.toCancelCommMonoidWithZero.{u2} A (CommRing.toCommSemiring.{u2} A _inst_5) _inst_6)] {K : Type.{u1}} [_inst_8 : Field.{u1} K] [_inst_9 : Algebra.{u2, u1} A K (CommRing.toCommSemiring.{u2} A _inst_5) (DivisionSemiring.toSemiring.{u1} K (Semifield.toDivisionSemiring.{u1} K (Field.toSemifield.{u1} K _inst_8)))] [_inst_10 : IsFractionRing.{u2, u1} A _inst_5 K (Field.toCommRing.{u1} K _inst_8) _inst_9] {x : K}, (Eq.{succ u2} A (IsFractionRing.num.{u2, u1} A _inst_5 _inst_6 _inst_7 K _inst_8 _inst_9 _inst_10 x) (OfNat.ofNat.{u2} A 0 (Zero.toOfNat0.{u2} A (CommMonoidWithZero.toZero.{u2} A (CancelCommMonoidWithZero.toCommMonoidWithZero.{u2} A (IsDomain.toCancelCommMonoidWithZero.{u2} A (CommRing.toCommSemiring.{u2} A _inst_5) _inst_6)))))) -> (Eq.{succ u1} K x (OfNat.ofNat.{u1} K 0 (Zero.toOfNat0.{u1} K (CommMonoidWithZero.toZero.{u1} K (CommGroupWithZero.toCommMonoidWithZero.{u1} K (Semifield.toCommGroupWithZero.{u1} K (Field.toSemifield.{u1} K _inst_8)))))))
Case conversion may be inaccurate. Consider using '#align is_fraction_ring.eq_zero_of_num_eq_zero IsFractionRing.eq_zero_of_num_eq_zeroₓ'. -/
theorem eq_zero_of_num_eq_zero {x : K} (h : num A x = 0) : x = 0 :=
  num_mul_den_eq_num_iff_eq'.mp (by rw [MulZeroClass.zero_mul, h, RingHom.map_zero])
#align is_fraction_ring.eq_zero_of_num_eq_zero IsFractionRing.eq_zero_of_num_eq_zero

/- warning: is_fraction_ring.is_integer_of_is_unit_denom -> IsFractionRing.isInteger_of_isUnit_den is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_fraction_ring.is_integer_of_is_unit_denom IsFractionRing.isInteger_of_isUnit_denₓ'. -/
theorem isInteger_of_isUnit_den {x : K} (h : IsUnit (den A x : A)) : IsInteger A x :=
  by
  cases' h with d hd
  have d_ne_zero : algebraMap A K (denom A x) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (denom A x).2
  use ↑d⁻¹ * Num A x
  refine' trans _ (mk'_num_denom A x)
  rw [map_mul, map_units_inv, hd]
  apply mul_left_cancel₀ d_ne_zero
  rw [← mul_assoc, mul_inv_cancel d_ne_zero, one_mul, mk'_spec']
#align is_fraction_ring.is_integer_of_is_unit_denom IsFractionRing.isInteger_of_isUnit_den

/- warning: is_fraction_ring.is_unit_denom_of_num_eq_zero -> IsFractionRing.isUnit_den_of_num_eq_zero is a dubious translation:
<too large>
Case conversion may be inaccurate. Consider using '#align is_fraction_ring.is_unit_denom_of_num_eq_zero IsFractionRing.isUnit_den_of_num_eq_zeroₓ'. -/
theorem isUnit_den_of_num_eq_zero {x : K} (h : num A x = 0) : IsUnit (den A x : A) :=
  num_den_reduced A x (h.symm ▸ dvd_zero _) dvd_rfl
#align is_fraction_ring.is_unit_denom_of_num_eq_zero IsFractionRing.isUnit_den_of_num_eq_zero

end NumDenom

variable (S)

end IsFractionRing

